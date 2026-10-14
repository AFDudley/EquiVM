import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorOptionalCallPost
import Benchmarks.Morpho.MetaMorphoV1_1.ZeroCallSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ByteMemoryPrefix
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorEncoding

/-! Shared source/EVM proof of the fallback optional-return token call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorOptionalCall {tail : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem data rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr dataPtr ret : UInt256} {R : List UInt256}
    (imms : Store) (token : AccountAddress)
    (hstack : R.length + 13 ≤ 1024) (hs : SourceState s0 I σ evm)
    (hptr : ptr.toNat < 2 ^ 64) (hlo : 96 ≤ ptr.toNat) (hdataSize : data.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hlen : memLoad dataPtr mem = UInt256.ofNat data.size)
    (hdata : mem.readWithPadding (dataPtr + UInt256.ofNat 32).toNat data.size = data)
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3692⟩
      (UInt256.ofNat token.toNat :: dataPtr :: ret :: R) mem aw rdata σ k C) :
    (ExecFuncBody config (optionalCallFrame imms token data ptr) evm
        allocatedOptionalReturnFunction.body .reverted ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
      ∃ (evm' : State) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
        SourceState s0 I evm'.accountMap evm' ∧ callReturnFits ptr out ∧
        ExecFuncBody config (optionalCallFrame imms token data ptr) evm
          allocatedOptionalReturnFunction.body
          (.returned (optionalResultFrame imms token data ptr out) evm'
            (some [uint256Value (callReturnCursor ptr out)])) ∧
        ByteMemoryPrefix mem (callReturnMemory mem ptr out) ptr.toNat ∧
        memLoad ⟨64⟩ (callReturnMemory mem ptr out) = callReturnCursor ptr out ∧
        RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret R (callReturnMemory mem ptr out) aw' out
          evm'.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1Creation_block_3692_packed
    (by simp only [List.length_cons]; omega) rd
  have hmask : UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.ofNat token.toNat) =
      UInt256.ofNat token.toNat := easWord_mask token
  simp only [metaMorphoV1_1Creation_block_3692_stack, hmask, hlen] at h1
  have hdec : decode (metaMorphoV1_1CreationBytecode ++ tail) ⟨3717⟩ = some (.CALL, none) :=
    decode_append_left_of_decode _ _ _ _ _ (by native_decide)
      (by rw [metaMorphoV1_1CreationBytecode_size]; native_decide) (by native_decide)
  obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', hout, h2⟩ :=
    zeroCallSimulation (by simp only [List.length_cons]; omega) hdec hs
      (show token = AccountAddress.ofUInt256 (UInt256.ofNat token.toNat) by
        symm
        rw [accountAddress_ofUInt256_eq_ofNat_toNat]
        exact accountAddress_of_word_val token)
      (by simpa only [UInt256.toNat_ofNat_of_lt hdataSize] using hdata) h1
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      change 0 ≤ (UInt256.ofNat out.size).toNat
      omega
    simp [min, hle]
  rw [hmin, byteArray_write_len_zero] at h2
  rcases constructorOptionalCallPost imms token hstack hptr hout hfree hzero hcall hret h2 with
    hbad | ⟨_, hfit, hsource, aw3, k3, C3, h3⟩
  · exact .inl hbad
  · exact .inr ⟨evm', out, aw3, k3, C3, hs', hfit, hsource,
      callReturnMemory_bytePrefix mem ptr out, callReturnMemory_free mem ptr out hlo hfree, h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
