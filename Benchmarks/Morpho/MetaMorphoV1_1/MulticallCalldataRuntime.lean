import Benchmarks.Morpho.MetaMorphoV1_1.BytesTailBounds
import Benchmarks.Morpho.MetaMorphoV1_1.CalldataBytesMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_022

/-! Decode and copy one multicall element, retaining every compiler failure branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def multicallElementMemory (mem cd : ByteArray) (ptr base : UInt256) (i : Nat) : ByteArray :=
  calldataBytesMemory mem cd ptr (bytesArrayHead cd base i + ⟨32⟩)
    (calldataWord cd (bytesArrayHead cd base i).toNat)

theorem multicallElementCopy {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C i : Nat}
    {ptr base : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 20 ≤ 1024) (hi : 32 * i < UInt256.size)
    (hsize : I.calldata.size < 2 ^ 255) (hfree : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (deployedRuntime v) I g s0 ⟨3886⟩
      (UInt256.ofNat i :: base :: ((UInt256.ofNat I.calldata.size - base) - ⟨31⟩) :: R)
      mem aw out σ k C) :
    let size := UInt256.ofNat (32 + (bytesTailData I.calldata (bytesArrayHead I.calldata base i)).size)
    ((¬ bytesArrayAccessValid I.calldata base i ∨ ¬ allocationFits ptr size) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (bytesArrayAccessValid I.calldata base i ∧ allocationFits ptr size ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨3951⟩
        (ptr :: ⟨0⟩ :: ⟨0⟩ :: ⟨3975⟩ :: UInt256.ofNat i :: ⟨1⟩ :: base ::
          ((UInt256.ofNat I.calldata.size - base) - ⟨31⟩) :: R)
        (multicallElementMemory mem I.calldata ptr base i) aw' out σ k' C') := by
  dsimp only
  rw [bytesTailData_size]
  let relative := bytesArrayRelative I.calldata base i
  let head := bytesArrayHead I.calldata base i
  let len := calldataWord I.calldata head.toNat
  let bound := (UInt256.ofNat I.calldata.size - base) - (⟨31⟩ : UInt256)
  have hshift : UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * i) := shiftLeft5_ofNat_eq hi
  have hr : uInt256OfByteArray (I.calldata.readBytes
      (base + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat 32) = relative := by
    rw [hshift]
    rfl
  by_cases hrel : UInt256.slt relative bound = ⟨0⟩
  case pos =>
    have r1 := metaMorphoV1_1_block_3886_taken (immWords := wordsOf (immStore v))
      (by (try simp only [List.length_cons]); omega) (by rw [hr, hrel]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨.inl (fun hc ↦ hc.1 hrel),
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_3886_taken_stack, List.length_cons]; omega) r1⟩
  have r1 := metaMorphoV1_1_block_3886_fallthrough (immWords := wordsOf (immStore v))
    (by (try simp only [List.length_cons]); omega) (by rw [hr]; exact isZero_eq_zero_of_ne hrel) rd
  simp only [metaMorphoV1_1_block_3886_fallthrough_stack, hr] at r1
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat ABI.solcMaxU64 := by decide +kernel
  by_cases hl : len.toNat ≤ ABI.solcMaxU64
  case neg =>
    have r2 := metaMorphoV1_1_block_3901_taken (immWords := wordsOf (immStore v))
      (by (try simp only [List.length_cons]); omega)
      (by rw [hmax]; change UInt256.gt len (UInt256.ofNat ABI.solcMaxU64) ≠ _
          rw [ugt_one (by change ABI.solcMaxU64 < len.toNat; omega)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact .inl ⟨.inl (fun hc ↦ hl hc.2.1),
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_3901_taken_stack, List.length_cons]; omega) r2⟩
  have r2 := metaMorphoV1_1_block_3901_fallthrough (immWords := wordsOf (immStore v))
    (by (try simp only [List.length_cons]); omega)
    (by rw [hmax]; exact ugt_zero hl) r1
  change RD (deployedRuntime v) I g s0 ⟨3921⟩
    (head :: UInt256.ofNat i :: len :: base :: bound :: R) mem _ out σ _ _ at r2
  by_cases hs : UInt256.sgt (head + ⟨32⟩) (UInt256.ofNat I.calldata.size - len) = ⟨0⟩
  case neg =>
    have r3 := metaMorphoV1_1_block_3921_taken (immWords := wordsOf (immStore v))
      (by (try simp only [List.length_cons]); omega)
      (by rw [u256_add_comm]; exact hs)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
    exact .inl ⟨.inl (fun hc ↦ hs (bytesTailValid_signedGuard hsize hc.2)),
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_3921_taken_stack, List.length_cons]; omega) r3⟩
  have r3 := metaMorphoV1_1_block_3921_fallthrough (immWords := wordsOf (immStore v))
    (by (try simp only [List.length_cons]); omega) (by rw [u256_add_comm]; exact hs) r2
  have r4 := metaMorphoV1_1_block_3933 (immWords := wordsOf (immStore v))
    (by (try simp only [List.length_cons]); omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r3
  simp only [metaMorphoV1_1_block_3933_stack, metaMorphoV1_1_block_3921_fallthrough_stack,
    u256_add_comm (UInt256.ofNat 32) head] at r4
  rcases calldataBytesAllocation v (by (try simp only [List.length_cons]); omega)
      (by change len.toNat ≤ 18446744073709551615 at hl; omega) hfree r4 with
    ⟨hbad, hrev⟩ | ⟨hfit, aw5, k5, C5, r5⟩
  · exact .inl ⟨.inr hbad, hrev⟩
  by_cases he : ((head + ⟨32⟩) + len).toNat ≤ (UInt256.ofNat I.calldata.size).toNat
  case neg =>
    exact .inl ⟨.inl (fun hc ↦ he hc.2.2),
      calldataBytesCopyRevert v (by (try simp only [List.length_cons]); omega) (Nat.lt_of_not_ge he) r5⟩
  obtain ⟨aw6, k6, C6, r6⟩ := calldataBytesCopyReturn v
    (by (try simp only [List.length_cons]); omega) he
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r5
  exact .inr ⟨⟨hrel, hl, he⟩, hfit, aw6, k6, C6, r6⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
