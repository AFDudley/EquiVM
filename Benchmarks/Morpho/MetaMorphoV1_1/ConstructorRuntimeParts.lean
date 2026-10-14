import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorRuntimeMemory
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_005
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_006
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainMemory

/-! Normalize the three creation blocks that copy and patch the deployed runtime. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem constructorRuntimeStart_eq {mem tail : ByteArray} {ptr : UInt256}
    {w : Nat → UInt256} (hm : 480 ≤ mem.size) (hlo : 480 ≤ ptr.toNat)
    (hfit : ptr.toNat + 19708 < UInt256.size) (hptr : memLoad ⟨64⟩ mem = ptr)
    (hr : ∀ off, 128 ≤ off → off + 32 ≤ 480 → memLoad (UInt256.ofNat off) mem = w off)
    (x0 x1 x2 x3 : UInt256) (R : List UInt256) :
    metaMorphoV1_1Creation_block_1153_stack (tail := tail) (mem := mem)
      (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := ⟨64⟩) (R := R) =
        UInt256.ofNat 13111 :: ptr :: w 320 :: ptr :: ⟨19708⟩ :: x0 :: x1 :: x2 :: x3 :: ⟨64⟩ :: R ∧
    metaMorphoV1_1Creation_block_1153_memory (tail := tail) (mem := mem) (x4 := ⟨64⟩) =
      constructorRuntimePart (constructorRuntimeCopy mem tail ptr) ptr w 0 9 := by
  have hc := constructorRuntimeCopy_prefix mem tail ptr
  have hcm : 480 ≤ (constructorRuntimeCopy mem tail ptr).size := le_trans hm hc.size
  have hread (off : Nat) (h1 : 128 ≤ off) (h2 : off + 32 ≤ 480) :
      memLoad (UInt256.ofNat off) (constructorRuntimeCopy mem tail ptr) = w off := by
    have hn : (UInt256.ofNat off).toNat = off := UInt256.toNat_ofNat_of_lt (by omega)
    exact (hc.load_preserved (by omega) (by omega) (by omega) (by omega)).trans (hr off h1 h2)
  have hwrite (m : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 m off 32 = writeWord m off word := rfl
  have hcopy : (metaMorphoV1_1CreationBytecode ++ tail).write 3894 mem ptr.toNat 19708 =
      constructorRuntimeCopy mem tail ptr := rfl
  have hadd (off : Nat) (hb : off ≤ 19708) :
      (UInt256.ofNat off + ptr).toNat = ptr.toNat + off := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat _ _ (by omega)
  unfold metaMorphoV1_1Creation_block_1153_stack metaMorphoV1_1Creation_block_1153_memory
  simp (disch := (first | omega | (simp (disch := decide) only
    [writeWord_sparse_size, UInt256.toNat_ofNat_of_lt]; omega))) only
    [UInt256.toNat_ofNat_of_lt, hwrite, hptr, hcopy, hadd, memLoad_writeWord_disjoint, hread]
  exact ⟨rfl, rfl⟩

theorem constructorRuntimeMiddle_eq {mem : ByteArray} {ptr : UInt256} {w : Nat → UInt256}
    (hm : 480 ≤ mem.size) (hlo : 480 ≤ ptr.toNat) (hfit : ptr.toNat + 19708 < UInt256.size)
    (hr : ∀ off, 128 ≤ off → off + 32 ≤ 480 → memLoad (UInt256.ofNat off) mem = w off)
    (R : List UInt256) :
    metaMorphoV1_1Creation_block_1251_stack (mem := mem)
      (x0 := UInt256.ofNat 13111) (x1 := ptr) (x2 := w 320) (x3 := ptr) (R := R) =
        ptr :: w 416 :: ptr :: w 416 :: ptr :: R ∧
    metaMorphoV1_1Creation_block_1251_memory (mem := mem)
      (x0 := UInt256.ofNat 13111) (x1 := ptr) (x2 := w 320) (x3 := ptr) =
        constructorRuntimePart mem ptr w 9 12 := by
  have hwrite (m : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 m off 32 = writeWord m off word := rfl
  have hadd (off : Nat) (hb : off ≤ 19708) :
      (UInt256.ofNat off + ptr).toNat = ptr.toNat + off := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat _ _ (by omega)
  unfold metaMorphoV1_1Creation_block_1251_stack metaMorphoV1_1Creation_block_1251_memory
  simp (disch := (first | omega | (simp (disch := decide) only
    [writeWord_sparse_size, UInt256.toNat_ofNat_of_lt]; omega))) only
    [hwrite, hadd, memLoad_writeWord_disjoint, hr]
  exact ⟨trivial, rfl⟩

theorem constructorRuntimeFinish {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr : UInt256} {σ : AccountMap} {k C : Nat}
    {w : Nat → UInt256} {R : List UInt256} (hstack : R.length + 7 ≤ 1024)
    (hm : 480 ≤ mem.size) (hlo : 480 ≤ ptr.toNat) (hfit : ptr.toNat + 19708 < UInt256.size)
    (hr : ∀ off, 128 ≤ off → off + 32 ≤ 480 → memLoad (UInt256.ofNat off) mem = w off)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1343⟩
      (ptr :: w 416 :: ptr :: w 416 :: ptr :: ⟨19708⟩ :: R) mem aw rdata σ k C) :
    RDret (metaMorphoV1_1CreationBytecode ++ tail) g s0 σ
      ((constructorRuntimePart mem ptr w 21 11).readWithPadding ptr.toNat 19708) := by
  have hwrite (m : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 m off 32 = writeWord m off word := rfl
  have hadd (off : Nat) (hb : off ≤ 19708) :
      (UInt256.ofNat off + ptr).toNat = ptr.toNat + off := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat _ _ (by omega)
  have h := metaMorphoV1_1Creation_block_1343 hstack rd
  simp (disch := (first | omega | (simp (disch := decide) only
    [writeWord_sparse_size, UInt256.toNat_ofNat_of_lt]; omega))) only
    [hwrite, hadd, memLoad_writeWord_disjoint, hr] at h
  exact h

end Benchmarks.Morpho.MetaMorphoV1_1
