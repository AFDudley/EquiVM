import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainLiterals
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainLiteralMemory
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsInit

/-! Initialize the ERC4626 immutable pair and encode both fixed EIP-712 literals. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
attribute [local irreducible] ConstructorArgs.encoded
set_option autoImplicit false

def constructorAssetReadyFrame (a : ConstructorArgs) (ok : Bool) (out : ByteArray) : Frame :=
  constructorAssetFrame (constructorDecimalsReadyFrame a ok out) a.asset ok out

def constructorAssetReadyMemory (mem : ByteArray) (a : ConstructorArgs) (ok : Bool)
    (out : ByteArray) : ByteArray :=
  writeWord (constructorAssetMemory mem a.asset (constructorUnderlyingDecimals ok out)) 352 ⟨0⟩

theorem constructorAssetReadySource (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (evm : State) {result : ExecResult}
    (htail : ExecBlock config (constructorAssetReadyFrame a ok out) evm
      (contract.ctor.body.drop 15) result) :
    ExecBlock config (constructorDecimalsReadyFrame a ok out) evm
      (contract.ctor.body.drop 13) result := by
  change ExecBlock config (constructorDecimalsReadyFrame a ok out) evm
    (.setImmutable "_underlyingDecimals" constructorUnderlyingExpr ::
      .setImmutable "_asset" (.var "assetAddress") :: contract.ctor.body.drop 15) result
  have hd : (constructorDecimalsReadyFrame a ok out).locals.get? "decimalResult" =
      some (constructorDecimalsValue ok out) :=
    cursorResultFrame_value _ _ _ _ (by decide)
  have ha : (constructorDecimalsReadyFrame a ok out).locals.get? "assetAddress" =
      some (.address a.asset) :=
    (cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)).trans
      (constructorInputFrame_asset a _)
  have hc : (constructorDecimalsReadyFrame a ok out).contract = contract := by
    simp only [constructorDecimalsReadyFrame, cursorResultFrame, constructorReadyFrame,
      constructorInputFrame_contract]
  exact constructorAssetSourcePrefix (frame := constructorDecimalsReadyFrame a ok out)
    (evm := evm) (asset := a.asset) (ok := ok) (out := out)
    (rest := contract.ctor.body.drop 15) hc hd ha htail

theorem constructorAssetInit {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {base mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (hlo : 480 ≤ a.stringsEnd) (hptr : a.stringsEnd + 160 < UInt256.size)
    (hp : ByteMemoryPrefix (constructorVersionMemory base a.stringsEnd) mem (a.stringsEnd + 160))
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨443⟩
      (constructorDecimalsWord ok out :: (if constructorDecimalsValid ok out then ⟨1⟩ else ⟨0⟩) ::
        constructorMetadataTail a a.stringsEnd true) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨479⟩
      (constructorVersionWord :: constructorMetadataTail a a.stringsEnd true)
      (constructorAssetReadyMemory mem a ok out) aw' rdata σ k' C' := by
  obtain ⟨hm, he, hew, hv, hvw⟩ := constructorPreservedLiteralReads base mem a.stringsEnd
    (by omega) hptr hp
  have hpreserve (off : Nat) (hoff : off ≤ 128) :
      memLoad (UInt256.ofNat (a.stringsEnd + off))
        (constructorAssetMemory mem a.asset (constructorUnderlyingDecimals ok out)) =
      memLoad (UInt256.ofNat (a.stringsEnd + off)) mem := by
    apply constructorAssetMemory_load
    · rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega
    · rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega
  obtain ⟨_, _, _, r1⟩ := constructorAssetRuntime a ok out rd
  exact constructorDomainLiterals
    (mem := constructorAssetMemory mem a.asset (constructorUnderlyingDecimals ok out)) a hlo hptr
    (by simp only [constructorAssetMemory, writeWord_sparse_size]; omega)
    ((hpreserve 0 (by omega)).trans he) ((hpreserve 32 (by omega)).trans hew)
    ((hpreserve 96 (by omega)).trans hv) ((hpreserve 128 (by omega)).trans hvw) r1

end Benchmarks.Morpho.MetaMorphoV1_1
