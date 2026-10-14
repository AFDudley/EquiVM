import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_057

/-! Shared runtime decoder for uint256,address,address. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem decodeUintTwoAddressesRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨96⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨11559⟩
      (UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_11559_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_11559_taken_stack, List.length_cons]; omega) h1

theorem decodeUintTwoAddresses {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hlen : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11559⟩
      (UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    (¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus ∧
      RDrev (deployedRuntime v) g s0) ∨
    ((calldataWord I.calldata 36).toNat < EVM.addressModulus ∧
      ¬ (calldataWord I.calldata 68).toNat < EVM.addressModulus ∧
      RDrev (deployedRuntime v) g s0) ∨
    ((calldataWord I.calldata 36).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata 68).toNat < EVM.addressModulus ∧
      ∃ k' C', RD (deployedRuntime v) I g s0 ret
        ([calldataWord I.calldata 68, calldataWord I.calldata 36,
          calldataWord I.calldata 4] ++ R) mem aw rdata σ k' C') := by
  have h1 := metaMorphoV1_1_block_11559_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨96⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk hlen hhi hsize (by decide)) rd
  by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
  · have h2 := metaMorphoV1_1_block_11572_fallthrough (immWords := wordsOf (immStore v))
      (by omega) (by
        change UInt256.sub (calldataWord I.calldata 36)
          (UInt256.land (calldataWord I.calldata 36) solcAddrMask) = ⟨0⟩
        exact addressSubMask_zero _ hc1) h1
    by_cases hc2 : (calldataWord I.calldata 68).toNat < EVM.addressModulus
    · have h3 := metaMorphoV1_1_block_11595_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by
          change UInt256.sub (calldataWord I.calldata 68)
            (UInt256.land (calldataWord I.calldata 68) solcAddrMask) = ⟨0⟩
          exact addressSubMask_zero _ hc2) h2
      have h4 := metaMorphoV1_1_block_11615 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hret h3
      exact .inr (.inr ⟨hc1, hc2, _, _, h4⟩)
    · have h3 := metaMorphoV1_1_block_11595_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by
          change UInt256.sub (calldataWord I.calldata 68)
            (UInt256.land (calldataWord I.calldata 68) solcAddrMask) ≠ ⟨0⟩
          exact addressSubMask_nonzero _ hc2)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
      exact .inr (.inl ⟨hc1, hc2, metaMorphoV1_1_block_917
        (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_11595_taken_stack, List.length_cons]; omega) h3⟩)
  · have h2 := metaMorphoV1_1_block_11572_taken (immWords := wordsOf (immStore v))
      (by omega) (by
        change UInt256.sub (calldataWord I.calldata 36)
          (UInt256.land (calldataWord I.calldata 36) solcAddrMask) ≠ ⟨0⟩
        exact addressSubMask_nonzero _ hc1)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    exact .inl ⟨hc1, metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_11572_taken_stack, List.length_cons]; omega) h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
