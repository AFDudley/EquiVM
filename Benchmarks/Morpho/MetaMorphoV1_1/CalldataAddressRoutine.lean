import Benchmarks.Morpho.MetaMorphoV1_1.Decode
/-! LIBRARY CANDIDATE: the shared address decoder at an arbitrary calldata offset. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem decodeAddressAt {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {offset ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata offset.toNat).toNat < EVM.addressModulus)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11207⟩ (offset :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (calldataWord I.calldata offset.toNat :: R) mem aw rdata σ k' C' := by
  have rd11184 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11207_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (calldataWord I.calldata offset.toNat)
        (UInt256.land (calldataWord I.calldata offset.toNat) solcAddrMask) = ⟨0⟩
      exact addressSubMask_zero _ hcanon) rd
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11226
    (immWords := wordsOf (immStore v))
    (by simpa only [List.length_cons] using (show R.length + 2 ≤ 1024 by omega))
    hvalid rd11184
  exact ⟨_, _, hret⟩

set_option maxRecDepth 2000 in
theorem decodeAddressAtRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {offset ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hnc : ¬ (calldataWord I.calldata offset.toNat).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨11207⟩ (offset :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11207_taken
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (calldataWord I.calldata offset.toNat)
        (UInt256.land (calldataWord I.calldata offset.toNat) solcAddrMask) ≠ ⟨0⟩
      exact addressSubMask_nonzero _ hnc)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v))
    (by simpa only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_11207_taken_stack,
      List.length_cons] using (show R.length + 1 + 1 + 2 ≤ 1024 by omega)) rd917

end Benchmarks.Morpho.MetaMorphoV1_1
