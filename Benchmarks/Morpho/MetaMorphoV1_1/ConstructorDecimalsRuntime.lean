import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsCall
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsResult
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorZeroMemory

/-! The optional decimals routine, including request and return allocation failures. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

def constructorDecimalsMemory (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  callReturnMemory (allocatedWordCallMemory mem ptr constructorDecimalsSelectorWord [])
    (nextCursor ptr ⟨36⟩) out

theorem constructorDecimalsMemory_prefix (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hfit : allocationFits ptr ⟨36⟩) :
    ByteMemoryPrefix mem (constructorDecimalsMemory mem ptr out) ptr.toNat :=
  (allocatedSelectorCall_bytePrefix mem ptr constructorDecimalsSelectorWord).trans
    ((callReturnMemory_bytePrefix _ _ out).mono hfit.2)

theorem constructorDecimalsMemory_free (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hlo : 96 ≤ ptr.toNat) (hfit : allocationFits ptr ⟨36⟩) :
    memLoad ⟨64⟩ (constructorDecimalsMemory mem ptr out) =
      callReturnCursor (nextCursor ptr ⟨36⟩) out :=
  callReturnMemory_free _ _ out (le_trans hlo hfit.2)
    (allocatedWordCallMemory_free mem ptr constructorDecimalsSelectorWord [])

theorem constructorDecimalsRuntime {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} (asset : AccountAddress)
    (hstack : R.length + 13 ≤ 1024) (hlo : 128 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hmem : 128 ≤ mem.size) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hs : SourceState s0 I σ evm)
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3545⟩
      (UInt256.ofNat asset.val :: ret :: R) mem aw rdata σ k C) :
    (¬ allocationFits ptr ⟨36⟩ ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (allocationFits ptr ⟨36⟩ ∧ ∃ (evm' : State) (ok : Bool) (out : ByteArray),
      typedCallViaEVM config evm asset "decimals" 0 [] (ok, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧
      ((¬ callReturnFits (nextCursor ptr ⟨36⟩) out ∧
        RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
       (callReturnFits (nextCursor ptr ⟨36⟩) out ∧ ∃ aw' k' C',
        RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret
          (constructorDecimalsWord ok out ::
            (if constructorDecimalsValid ok out then ⟨1⟩ else ⟨0⟩) :: R)
          (constructorDecimalsMemory mem ptr out) aw' out evm'.accountMap k' C'))) := by
  rcases constructorDecimalsRequest asset (by simp only [List.length_cons]; omega)
    (by omega) hptr hfree rd with hfail | ⟨hfit, gasArg, aw1, k1, C1, r1⟩
  · exact .inl hfail
  obtain ⟨evm', ok, out, aw2, k2, C2, hc, hs', hout, r2⟩ :=
    constructorDecimalsStaticcall asset (by simp only [List.length_cons]; omega)
      (by omega) hptr hs r1
  refine .inr ⟨hfit, evm', ok, out, hc, hs', ?_⟩
  obtain ⟨_, _, _, r3⟩ := metaMorphoV1_1Creation_block_3595_packed
    (by simp only [List.length_cons]; omega) (by native_decide) r2
  rcases constructorCallReturnBuffer (by simp only [List.length_cons]; omega)
    hfit.1 hout (allocatedWordCallMemory_free mem ptr constructorDecimalsSelectorWord [])
    (by native_decide) r3 with hfail | ⟨hreturn, aw4, k4, C4, r4⟩
  · exact .inl hfail
  have hz : memLoad ⟨96⟩ (allocatedWordCallMemory mem ptr constructorDecimalsSelectorWord []) = ⟨0⟩ :=
    ((allocatedSelectorCall_bytePrefix mem ptr constructorDecimalsSelectorWord).load ⟨96⟩
      (by decide) hlo hmem).trans hzero
  have hsmall : out.size < 2 ^ 255 := by
    rcases hreturn with he | ⟨hb, _⟩ <;> omega
  obtain ⟨aw5, k5, C5, r5⟩ := constructorDecimalsResult ok (by omega) hsmall
    (callReturnMemory_length _ _ out hz)
    (fun hl => by
      rw [u256_add_comm]
      exact callReturnMemory_word _ _ out hl (by have := hfit.1; change _ < 2 ^ 256; omega))
    hret r4
  exact .inr ⟨hreturn, aw5, k5, C5, r5⟩

end Benchmarks.Morpho.MetaMorphoV1_1
