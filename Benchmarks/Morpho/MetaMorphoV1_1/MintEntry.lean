import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_026

/-! Mint entry guards and the address decoder before interest accrual. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem mintReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hlen : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨4789⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11185⟩
      ([⟨4822⟩, ⟨1578⟩, calldataWord I.calldata 4, ⟨32⟩] ++ R) mem aw rdata σ k' C' := by
  have h1 := metaMorphoV1_1_block_4789_fallthrough (immWords := wordsOf (immStore v))
    (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_4795_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨64⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_64 hlen hhi hsize) h1
  exact ⟨_, _, metaMorphoV1_1_block_4807 (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2⟩

theorem mintRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨4789⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_4789_taken (immWords := wordsOf (immStore v))
    hstack hwv (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h1

theorem mintRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨64⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨4789⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_4789_fallthrough (immWords := wordsOf (immStore v))
    (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_4795_taken (immWords := wordsOf (immStore v))
    hstack hcond (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h2

theorem mintReachAccrual {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hlen : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨4789⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨14262⟩
      ([⟨4831⟩, calldataWord I.calldata 4, ⟨1578⟩, calldataWord I.calldata 36, ⟨32⟩] ++ R)
      mem aw rdata σ k' C' := by
  obtain ⟨k1, C1, h1⟩ := mintReachDecoder v (by omega) hwv hlen hhi hsize rd
  obtain ⟨k2, C2, h2⟩ := decodeAddressAt36 v
    (by simp only [List.append, List.length_cons]; omega) hcanon
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  exact ⟨_, _, metaMorphoV1_1_block_4822 (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
