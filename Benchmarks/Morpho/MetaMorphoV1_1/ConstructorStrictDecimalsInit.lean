import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorMorphoContext
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStrictDecimalsMemory
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStrictDecimalsAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStrictDecimalsSource

/-! Couple the symbol event, MORPHO assignment, and strict decimals call with the source. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorStrictDecimalsPtr (a : ConstructorArgs) (out : ByteArray) : UInt256 :=
  UInt256.ofNat ((constructorDecimalsCursor a out).toNat + 192)

def constructorFinalDecimalsFrame (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) (strictOut : ByteArray) : Frame :=
  constructorStrictDecimalsFrame (constructorMorphoReadyFrame a ok out I)
    (constructorStrictDecimalsPtr a out) strictOut

def constructorFinalDecimalsMemory (mem : ByteArray) (a : ConstructorArgs)
    (out strictOut : ByteArray) : ByteArray :=
  constructorStrictDecimalsMemory (constructorMorphoMemory mem a.morpho (constructorStrictDecimalsPtr a out))
    (constructorStrictDecimalsPtr a out) strictOut

theorem constructorStrictDecimalsInit {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata : ByteArray} {aw finish : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true) (hmem : 96 ≤ mem.size)
    (hlo : 480 ≤ (constructorDecimalsCursor a out).toNat + 192)
    (hfreeBound : (constructorDecimalsCursor a out).toNat + 192 < 2 ^ 64)
    (hfree : memLoad ⟨64⟩ mem = constructorStrictDecimalsPtr a out)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1010⟩
      [finish, constructorStrictDecimalsPtr a out, constructorStrictDecimalsPtr a out,
        stringSetTopic true, UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]
      mem aw rdata σ k C) :
    (ExecBlock config (constructorTimelockReadyFrame a ok out I) evm (contract.ctor.body.drop 32) .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    ∃ (evm' : State) (strictOut : ByteArray) (aw' : UInt256) (k' C' : Nat),
      32 ≤ strictOut.size ∧ strictOut.size < 2 ^ 138 ∧
      (calldataWord strictOut 0).toNat < 256 ∧ allocationFits (constructorStrictDecimalsPtr a out) ⟨32⟩ ∧
      SourceState s0 I evm'.accountMap evm' ∧
      (∀ result, ExecBlock config (constructorFinalDecimalsFrame a ok out I strictOut) evm'
          (contract.ctor.body.drop 36) result →
        ExecBlock config (constructorTimelockReadyFrame a ok out I) evm
          (contract.ctor.body.drop 32) result) ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1053⟩
        [⟨255⟩, calldataWord strictOut 0, UInt256.ofNat a.asset.val,
          UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]
        (constructorFinalDecimalsMemory mem a out strictOut) aw' strictOut evm'.accountMap k' C' := by
  have hp : (constructorStrictDecimalsPtr a out).toNat =
      (constructorDecimalsCursor a out).toNat + 192 :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)
  obtain ⟨_, _, _, _, r1⟩ := constructorMorphoRequest a hperm hmem hfree rd
  obtain ⟨evm', ok', out', _, _, _, hcall, hs', hout, r2⟩ :=
    constructorStrictDecimalsCall a.asset (by simp) hs r1
  have hout' : out'.size < UInt256.size := by change _ < 2 ^ 256; omega
  have hsrcFail (hbad : ¬ (ok' = true ∧ 32 ≤ out'.size ∧
      (calldataWord out' 0).toNat < 256 ∧ allocationFits (constructorStrictDecimalsPtr a out) ⟨32⟩)) :
      ExecBlock config (constructorTimelockReadyFrame a ok out I) evm
        (contract.ctor.body.drop 32) .reverted := by
    apply constructorMorphoPrefix a ok out I
    rw [constructorStrictDecimalsBodySplit]
    exact execBlock_append_term
      (constructorStrictDecimalsRevert (constructorMorphoReadyFrame_contract a ok out I)
        (constructorMorphoReadyFrame_cursor a ok out I)
        (constructorMorphoReadyFrame_asset a ok out I) hcall (by omega) hbad)
      (by intros; simp)
  cases ok' with
  | false => exact .inl ⟨hsrcFail (by simp), constructorStrictDecimalsFailure a hout' r2⟩
  | true =>
    rcases constructorStrictDecimalsAllocation a hout' r2 with hfail | hready
    · exact .inl ⟨hsrcFail (fun h => hfail.1 ⟨h.2.1, h.2.2.2⟩), hfail.2⟩
    · obtain ⟨hl, hf, _, _, _, r3⟩ := hready
      have hw : memLoad (constructorStrictDecimalsPtr a out)
          (constructorFinalDecimalsMemory mem a out out') = calldataWord out' 0 :=
        constructorStrictDecimalsMemory_word
          (by simp only [constructorMorphoMemory, writeWord_sparse_size]; omega)
          (by rw [hp]; omega) (by rw [hp]; exact hfreeBound) hl hout'
      rcases constructorStrictDecimalsRead a hw r3 with hbad | hgood
      · exact .inl ⟨hsrcFail (fun h => hbad.1 h.2.2.1), hbad.2⟩
      · obtain ⟨hv, aw4, k4, C4, r4⟩ := hgood
        refine .inr ⟨evm', out', aw4, k4, C4, hl, hout, hv, hf, hs', ?_, r4⟩
        intro result htail
        apply constructorMorphoPrefix a ok out I
        rw [constructorStrictDecimalsBodySplit]
        exact execBlock_append
          (constructorStrictDecimalsSuccess (constructorMorphoReadyFrame_contract a ok out I)
            (constructorMorphoReadyFrame_cursor a ok out I)
            (constructorMorphoReadyFrame_asset a ok out I) hcall (by omega) ⟨hl, hv, hf⟩) htail

end Benchmarks.Morpho.MetaMorphoV1_1
