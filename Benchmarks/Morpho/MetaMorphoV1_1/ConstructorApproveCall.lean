import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorApproveRequest
import Benchmarks.Morpho.MetaMorphoV1_1.ZeroCallSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.BoundedCallMemory

/-! Couple the first approval CALL to the source without copying an inline return window. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorApproveCall {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr gasArg : UInt256} {R : List UInt256} (asset spender : AccountAddress)
    (hstack : R.length + 1 ≤ 1024) (hptr : ptr.toNat < 2 ^ 64)
    (hbuffer : BytesBuffer mem ptr (constructorApproveCalldata spender constructorApprovalValue))
    (hs : SourceState s0 I σ evm)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1126⟩
      (gasArg :: UInt256.ofNat asset.val :: ⟨0⟩ :: (ptr + ⟨32⟩) :: ⟨68⟩ :: ⟨0⟩ :: ⟨0⟩ :: R)
      mem aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      callViaEVM evm asset 0 (constructorApproveCalldata spender constructorApprovalValue)
        (ok, evm', out) ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < 2 ^ 138 ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1127⟩
        ((if ok then ⟨1⟩ else ⟨0⟩) :: R) mem aw' out evm'.accountMap k' C' := by
  have hp : (ptr + (⟨32⟩ : UInt256)).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  obtain ⟨evm', ok, out, aw', k', C', hc, hs', _, r1⟩ :=
    zeroCallSimulation (address := asset)
      (data := constructorApproveCalldata spender constructorApprovalValue) hstack
      (decode_append_left_of_decode _ _ _ _ _ (by native_decide)
        (by rw [metaMorphoV1_1CreationBytecode_size]; native_decide) (by native_decide))
      hs
      (by rw [accountAddress_ofUInt256_eq_ofNat_toNat]; exact (addressOfWordOfNat _).symm)
      (by rw [hp]; simpa only [constructorApproveCalldata_size] using hbuffer.data) rd
  have hmin : min (⟨0⟩ : UInt256) (UInt256.ofNat out.size) = ⟨0⟩ := by
    apply u256_inj
    change min 0 (UInt256.ofNat out.size).toNat = 0
    exact Nat.zero_min _
  simp only [hmin, show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_write_len_zero] at r1
  exact ⟨evm', ok, out, aw', k', C', hc, hs',
    callViaEVM_output_bound hc (by rw [constructorApproveCalldata_size]; decide), r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
