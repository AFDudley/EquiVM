import Benchmarks.Morpho.MetaMorphoV1_1.UintTwoAddressesDecoder
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_018

/-! Public redeemal entry guard and the route to the shared calldata decoder. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem redeemReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨2947⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11559⟩
      ([UInt256.ofNat I.calldata.size, ⟨2966⟩, ⟨1578⟩, ⟨32⟩] ++ R)
      mem aw rdata σ k' C' := by
  have h1 := metaMorphoV1_1_block_2947_fallthrough (immWords := wordsOf (immStore v))
    (by omega) hwv rd
  exact ⟨_, _, metaMorphoV1_1_block_2953 (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1⟩

theorem redeemRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨2947⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_2947_taken (immWords := wordsOf (immStore v))
    hstack hwv (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h1

end Benchmarks.Morpho.MetaMorphoV1_1
