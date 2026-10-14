import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainCache
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainInputs
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorOwnerSource

/-! Couple domain initialization and its two failure branches with the constructor source. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorDomainReadyFrame (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) : Frame :=
  constructorDomainCachedFrame
    (constructorDomainReservedFrame (constructorAssetReadyFrame a ok out) (constructorDecimalsCursor a out)) I

def constructorDomainReadyMemory (mem : ByteArray) (a : ConstructorArgs) (ok : Bool)
    (out : ByteArray) (I : ExecutionEnv) : ByteArray :=
  constructorDomainCachedMemory (constructorAssetReadyMemory mem a ok out) I
    (constructorDecimalsCursor a out).toNat

theorem constructorDomainInit {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {base mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ok : Bool) (out : ByteArray) (henv : evm.executionEnv = I)
    (hlo : 480 ≤ a.stringsEnd) (hptr : a.stringsEnd + 160 < UInt256.size)
    (hp : ByteMemoryPrefix (constructorVersionMemory base a.stringsEnd) mem (a.stringsEnd + 160))
    (hcursorBound : (constructorDecimalsCursor a out).toNat < 2 ^ 64)
    (hcursorLo : a.stringsEnd + 160 ≤ (constructorDecimalsCursor a out).toNat)
    (hfree : memLoad ⟨64⟩ mem = constructorDecimalsCursor a out)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨479⟩
      (constructorVersionWord :: constructorMetadataTail a a.stringsEnd true)
      (constructorAssetReadyMemory mem a ok out) aw rdata σ k C) :
    (ExecBlock config (constructorAssetReadyFrame a ok out) evm (contract.ctor.body.drop 15) .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) g s0) ∨
    (a.owner ≠ ⟨0, by decide⟩ ∧ (constructorDecimalsCursor a out).toNat + 192 < 2 ^ 64 ∧
      (∀ result, ExecBlock config (constructorDomainReadyFrame a ok out I) evm
          (contract.ctor.body.drop 25) result →
        ExecBlock config (constructorAssetReadyFrame a ok out) evm (contract.ctor.body.drop 15) result) ∧
      ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨616⟩
        (constructorOwnershipTail a) (constructorDomainReadyMemory mem a ok out I) aw' rdata σ k' C') := by
  have hc : (constructorAssetReadyFrame a ok out).contract = contract := by
    simp only [constructorAssetReadyFrame, constructorAssetFrame, constructorDecimalsReadyFrame,
      cursorResultFrame, constructorReadyFrame, constructorInputFrame_contract]
  have hcursor : (constructorAssetReadyFrame a ok out).locals.get? cursorName =
      some (uint256Value (constructorDecimalsCursor a out)) := by
    simpa only [constructorAssetReadyFrame, constructorAssetFrame, constructorDecimalsReadyFrame] using
      cursorResultFrame_cursor (constructorReadyFrame a) "decimalResult"
        (constructorDecimalsValue ok out) (constructorDecimalsCursor a out)
  have hm : 96 ≤ mem.size := by
    have hsize := (constructorPreservedLiteralReads base mem a.stringsEnd (by omega) hptr hp).1
    omega
  obtain ⟨he, hv⟩ := constructorDomainInputs base mem a ok out hlo hptr hp
  have hf : memLoad ⟨64⟩ (constructorAssetReadyMemory mem a ok out) =
      UInt256.ofNat (constructorDecimalsCursor a out).toNat := by
    rw [constructorAssetReadyMemory_free mem a ok out hm, hfree, u256_ofNat_toNat]
  rcases constructorDomainAllocation a (constructorDecimalsCursor a out).toNat hlo hptr
    hcursorBound he hv hf rd with hfail | halloc
  · refine .inl ⟨?_, hfail.2⟩
    rw [constructorDomainBodySplit]
    exact constructorDomainReserveReverts hc hcursor
      (by simpa only [u256_ofNat_toNat] using hfail.1) _
  · obtain ⟨hfit, aw1, k1, C1, r1⟩ := halloc
    have hfit' : allocationFits (constructorDecimalsCursor a out) ⟨192⟩ := by
      simpa only [u256_ofNat_toNat] using hfit
    have hsum : (constructorDecimalsCursor a out).toNat + 192 < 2 ^ 64 := by
      have hsum := (allocationFits_iff_sum_lt _ _).mp hfit'
      exact hsum
    have hrc : (constructorDomainReservedFrame (constructorAssetReadyFrame a ok out)
        (constructorDecimalsCursor a out)).contract = contract := by
      simpa only [constructorDomainReservedFrame, constructorDomainConstantsFrame] using hc
    have hrn : (constructorDomainReservedFrame (constructorAssetReadyFrame a ok out)
        (constructorDecimalsCursor a out)).immutables.get? "_hashedName" =
        some (uint256Value constructorNameHash) := by
      simpa only [constructorDomainReservedFrame] using
        constructorDomainConstantsFrame_name (constructorAssetReadyFrame a ok out)
    have hrv : (constructorDomainReservedFrame (constructorAssetReadyFrame a ok out)
        (constructorDecimalsCursor a out)).immutables.get? "_hashedVersion" =
        some (uint256Value constructorVersionHash) := by
      simpa only [constructorDomainReservedFrame] using
        constructorDomainConstantsFrame_version (constructorAssetReadyFrame a ok out)
    have hro : (constructorDomainReservedFrame (constructorAssetReadyFrame a ok out)
        (constructorDecimalsCursor a out)).locals.get? "owner" = some (.address a.owner) := by
      rw [constructorDomainReservedFrame, store_get_ne _ _ (by decide)]
      exact constructorAssetReadyFrame_owner a ok out
    rcases constructorDomainCache a (constructorDecimalsCursor a out).toNat (by omega) hcursorBound r1 with
      hzero | hcache
    · refine .inl ⟨?_, hzero.2⟩
      rw [constructorDomainBodySplit]
      apply constructorDomainReservePrefix hc hcursor hfit'
      rw [constructorDomainCacheBodySplit]
      exact constructorDomainOwnerReverts hrc hrn hrv hro hzero.1 _
    · refine .inr ⟨hcache.1, hsum, ?_, hcache.2⟩
      intro result htail
      rw [constructorDomainBodySplit]
      apply constructorDomainReservePrefix hc hcursor hfit'
      rw [constructorDomainCacheBodySplit]
      apply constructorDomainOwnerPrefix hrc hrn hrv hro hcache.1
      simpa only [henv, constructorDomainReadyFrame] using htail

end Benchmarks.Morpho.MetaMorphoV1_1
