import Benchmarks.EAS.EAS.ArrayTableMemory
import Benchmarks.EAS.EAS.AttestAllocationRequests
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem WordArrayTablePrefix.write_below {mem : ByteArray} {ptr : UInt256}
    {groups : List (List UInt256)} {filled limit : Nat} (h : WordArrayTablePrefix mem ptr groups filled limit)
    (dst : Nat) (word : UInt256) (hlo : dst+32 ≤ ptr.toNat) (hb : limit < UInt256.size) :
    WordArrayTablePrefix (Reasoning.Theory.writeWord mem dst word) ptr groups filled limit := by
  have hs := h.span
  have hc := h.covered
  refine ⟨h.low,h.progress,h.span,by rw [writeWord_sparse_size]; omega,?_,?_⟩
  · exact (memLoad_write_above _ _ _ _ hlo (by omega)).trans h.length
  · intro i hi
    have hslot : (UInt256.ofNat (ptr.toNat+32+32*i)).toNat = ptr.toNat+32+32*i :=
      ulit_toNat' _ (by have := h.progress; omega)
    obtain ⟨p,hp,hv,hlo'⟩ := h.arrays i hi
    exact ⟨p,(memLoad_write_above _ _ _ _ (by rw [hslot]; omega) (by rw [hslot]; have := h.progress; omega)).trans hp,
      hv.write_disjoint _ _ hb (Or.inr (by omega)),hlo'⟩

theorem attestAllocationMemory_table {mem : ByteArray} {heap table data : UInt256}
    {groups : List (List UInt256)} {filled : Nat} (kind : AttestCallKind) (attester : UInt256)
    (h : WordArrayTablePrefix mem table groups filled heap.toNat) (hlo : 224 ≤ table.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hn : allocateNext heap.toNat 128 ≤ 2^64-1) :
    WordArrayTablePrefix (attestAllocationMemory kind mem heap data attester) table groups filled heap.toNat := by
  have he : WordArrayTablePrefix (attestEntryMemory kind mem data attester) table groups filled heap.toNat := by
    cases kind with
    | single => exact h
    | many => exact (h.write_below 192 data hlo heap.val.isLt).write_below 160 attester (by omega) heap.val.isLt
  have hp := (attestResultsMemory_view (attestEntryMemory kind mem data attester) heap
    (by have := h.span; omega) hh hn).1
  have ha := he.preserve hp (le_refl _) heap.val.isLt
  cases kind with
  | single => exact ha
  | many => exact ha.write_below 128 (UInt256.ofNat (allocateNext heap.toNat 64)) (by omega) heap.val.isLt

theorem arrayTableAllocationMemory_zero96 (n : Nat) :
    memLoad (UInt256.ofNat 96)
      (arrayTableAllocationMemory (Reasoning.Theory.writeWord ByteArray.empty 64 (UInt256.ofNat 224)) (UInt256.ofNat 224) n) = ⟨0⟩ := by
  let pre := Reasoning.Theory.writeWord (Reasoning.Theory.writeWord ByteArray.empty 64 (UInt256.ofNat 224))
    64 (UInt256.ofNat (allocateNext 224 (32+32*n)))
  have hs : pre.size = 96 := by simp only [pre,writeWord_sparse_size]; rfl
  let header := Reasoning.Theory.writeWord pre 224 (UInt256.ofNat n)
  have hc : 256 ≤ header.size := by dsimp only [header]; rw [writeWord_sparse_size]; omega
  have hz : header.readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray := by
    dsimp only [header]
    rw [writeWord_sparse_eq _ _ _ (by rw [hs]; decide)]
    exact zeroBlock_read _ _ _ _ (by rw [hs]) (by rw [hs]; decide)
  have hg := writeWordSequence_grows header 256 (List.replicate n (UInt256.ofNat 96))
  apply mloadWordValue_of_readWithPadding
  · change 96 < (writeWordSequence header 256 (List.replicate n (UInt256.ofNat 96))).size
    omega
  · change (writeWordSequence header 256 (List.replicate n (UInt256.ofNat 96))).readWithPadding 96 32 = _
    rw [writeWordSequence_read_below _ _ _ _ (by omega) (by decide),hz]

end Benchmarks.EAS.EAS
