import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsRequest
import Benchmarks.Morpho.MetaMorphoV1_1.StaticCallSimulation

/-! Share the constructor's actual optional decimals STATICCALL with the source. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorDecimalsStaticcall {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr gasArg : UInt256} {R : List UInt256} (asset : AccountAddress)
    (hstack : R.length + 1 ≤ 1024) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hs : SourceState s0 I σ evm)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3594⟩
      (gasArg :: UInt256.ofNat asset.val :: (ptr + ⟨32⟩) :: ⟨4⟩ :: ⟨0⟩ :: ⟨0⟩ :: R)
      (allocatedWordCallMemory mem ptr constructorDecimalsSelectorWord []) aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm asset "decimals" 0 [] (ok, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < UInt256.size ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3595⟩
        ((if ok then ⟨1⟩ else ⟨0⟩) :: R)
        (allocatedWordCallMemory mem ptr constructorDecimalsSelectorWord []) aw' out evm'.accountMap k' C' := by
  have hp : (ptr + (⟨32⟩ : UInt256)).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  have hr := (allocatedSelectorCall_buffer mem ptr constructorDecimalsSelectorWord hlo).data
  simp only [ByteArray.size_extract, toByteArray_size] at hr
  obtain ⟨evm', ok, out, aw', k', C', hc, hs', hout, r1⟩ :=
    typedStaticcallSimulation (cfg := config) (address := asset) (name := "decimals") (args := [])
      hstack
      (decode_append_left_of_decode _ _ _ _ _ (by native_decide)
        (by rw [metaMorphoV1_1CreationBytecode_size]; native_decide) (by native_decide))
      hs
      (by rw [accountAddress_ofUInt256_eq_ofNat_toNat]; exact (addressOfWordOfNat _).symm)
      (by
        rw [constructorDecimalsEncode, hp]
        congr 1
        exact hr.symm)
      rd
  have hmin : min (⟨0⟩ : UInt256) (UInt256.ofNat out.size) = ⟨0⟩ := by
    apply u256_inj
    change min 0 (UInt256.ofNat out.size).toNat = 0
    exact Nat.zero_min _
  simp only [hmin, show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_write_len_zero] at r1
  exact ⟨evm', ok, out, aw', k', C', hc, hs', hout, r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
