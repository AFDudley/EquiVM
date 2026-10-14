import Benchmarks.Morpho.MetaMorphoV1_1.OptionalCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorOptionalReturn
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorAddressVerify
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorCallReturn
import Benchmarks.Morpho.MetaMorphoV1_1.AddressVerifyBuffer

/-! Match fallback call failures, return allocation, target validation, and optional Boolean checks. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorOptionalCallPost {tail : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 evm evm' : State}
    {mem data out : ByteArray} {aw : UInt256} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} {ok : Bool}
    (imms : Store) (token : AccountAddress)
    (hstack : R.length + 13 ≤ 1024) (hptr : ptr.toNat < 2 ^ 64)
    (hout : out.size < UInt256.size) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hcall : callViaEVM evm token 0 data (ok, evm', out))
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3718⟩
      ((if ok then ⟨1⟩ else ⟨0⟩) :: ⟨3732⟩ :: UInt256.ofNat token.toNat :: ret :: R)
      mem aw out evm'.accountMap k C) :
    (ExecFuncBody config (optionalCallFrame imms token data ptr) evm
        allocatedOptionalReturnFunction.body .reverted ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
      (ok = true ∧ callReturnFits ptr out ∧
        ExecFuncBody config (optionalCallFrame imms token data ptr) evm
          allocatedOptionalReturnFunction.body
          (.returned (optionalResultFrame imms token data ptr out) evm'
            (some [uint256Value (callReturnCursor ptr out)])) ∧
        ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret R
          (callReturnMemory mem ptr out) aw' out evm'.accountMap k' C') := by
  have h1 := metaMorphoV1_1Creation_block_3718
    (by simp only [List.length_cons]; omega)
    (by native_decide) rd
  rcases constructorCallReturnBuffer (by
      simp only [metaMorphoV1_1Creation_block_3718_stack, List.length_cons]; omega) hptr hout hfree
      (by native_decide) h1 with
    ⟨hbad, hrev⟩ | ⟨hfit, aw2, k2, C2, h2⟩
  · exact .inl ⟨optionalCallBodyRevertsAddress imms token data ptr ok out hcall (.inl hbad), hrev⟩
  · have h3 := metaMorphoV1_1Creation_block_3725
      (by simp only [List.length_cons]; omega)
      (by native_decide) h2
    have hlen := callReturnMemory_length mem ptr out hzero
    have hword := callReturnMemory_word mem ptr out
    have hp32 : ptr.toNat + 32 < UInt256.size := by change _ < 2 ^ 256; omega
    cases ok with
    | false =>
        exact .inl ⟨optionalCallBodyRevertsAddress imms token data ptr false out hcall
            (.inr (.inl rfl)), constructorAddressVerifyRevertCall
              (by simp only [List.length_cons]; omega) h3⟩
    | true =>
        by_cases hv : addressReturnValid evm' token out
        · obtain ⟨aw4, k4, C4, h4⟩ := constructorAddressVerifyReturn
            (by simp only [List.length_cons]; omega)
            ((addressReturnValid_memory hout hzero).mp hv)
            (by native_decide) h3
          have hs : out.size < 2 ^ 64 := by rcases hfit with hz | ⟨hs, _⟩ <;> omega
          rcases constructorOptionalReturn (by omega) hs hlen
              (fun hl ↦ hword hl hp32) hret h4 with hbad | hgood
          · exact .inl ⟨optionalCallBodyRevertsBool imms token data ptr out hcall hfit hv hbad.1,
              hbad.2⟩
          · exact .inr ⟨rfl, hfit,
              optionalCallBodyReturns imms token data ptr out hcall hfit hv hgood.1, hgood.2⟩
        · have hz : out.size = 0 := not_not.mp (fun hn ↦ hv (.inl hn))
          have hc : extCodeSizeWord evm'.accountMap (UInt256.ofNat token.toNat) = ⟨0⟩ :=
            not_not.mp (fun hn ↦ hv (.inr hn))
          exact .inl ⟨optionalCallBodyRevertsAddress imms token data ptr true out hcall
              (.inr (.inr hv)), constructorAddressVerifyRevertCode
                (by simp only [List.length_cons]; omega) (by simpa only [hz] using hlen) hc h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
