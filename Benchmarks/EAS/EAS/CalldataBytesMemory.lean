import Benchmarks.EAS.EAS.CalldataCopy
import Benchmarks.EAS.EAS.ByteViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: allocation, length, CALLDATACOPY, and the final zero word.
def calldataBytesMemory (mem cd : ByteArray) (src heap len : Nat) (next : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord
    (cd.write src (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 64 next) heap (UInt256.ofNat len))
      (heap+32) len)
    (heap+32+len) ⟨0⟩

theorem calldataBytesMemory_views (mem cd : ByteArray) (src heap len : Nat) (next : UInt256)
    (hsrc : len=0 ∨ src+len ≤ cd.size) (hlo : 96 ≤ heap) (hb : heap < UInt256.size) :
    MemoryPrefix mem (calldataBytesMemory mem cd src heap len next) heap ∧
    heap+32+32*((len+31)/32) ≤ (calldataBytesMemory mem cd src heap len next).size ∧
    memLoad (UInt256.ofNat 64) (calldataBytesMemory mem cd src heap len next) = next ∧
    memLoad (UInt256.ofNat heap) (calldataBytesMemory mem cd src heap len next) = UInt256.ofNat len ∧
    (calldataBytesMemory mem cd src heap len next).readWithPadding (heap+32) len = cd.readBytes src len := by
  let m1 := Reasoning.Theory.writeWord mem 64 next
  let m2 := Reasoning.Theory.writeWord m1 heap (UInt256.ofNat len)
  let m3 := cd.write src m2 (heap+32) len
  let m4 := Reasoning.Theory.writeWord m3 (heap+32+len) ⟨0⟩
  have h1 : 96 ≤ m1.size := by dsimp only [m1]; rw [writeWord_sparse_size]; omega
  have h2 : heap+32 ≤ m2.size := by dsimp only [m2]; rw [writeWord_sparse_size]; omega
  have h2low : 96 ≤ m2.size := by omega
  have h3 : m2.size ≤ m3.size := byteArray_write_size_ge_base _ _ _ _ _
  have hpayload := calldataCopy_payload cd m2 src (heap+32) len hsrc h2
  have h34 : MemoryPrefix m2 m4 (heap+32) :=
    (calldataCopy_prefix cd m2 src (heap+32) len (heap+32) hsrc h2 (le_refl _)).trans
      (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))
  have hprefix : MemoryPrefix mem m4 heap :=
    ((memoryPrefix_sparse_writeWord mem 64 heap next (Or.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord m1 heap heap (UInt256.ofNat len) (Or.inl (le_refl _)))).trans
      (h34.mono (by omega))
  refine ⟨hprefix,?_,?_,?_,?_⟩
  · change heap+32+32*((len+31)/32) ≤ m4.size
    dsimp only [m4]
    rw [writeWord_sparse_size]
    omega
  · apply mloadWordValue_of_readWithPadding
    · change 64 < m4.size
      exact lt_of_lt_of_le (by omega) h34.size
    · change m4.readWithPadding 64 32 = next.toByteArray
      dsimp only [m4]
      rw [writeWord_read_below_len _ _ _ _ _ (by omega) (by omega)]
      rw [calldataCopy_read cd m2 src (heap+32) len 64 hsrc h2 h2low (Or.inl (by omega))]
      dsimp only [m2]
      rw [writeWord_read_below_len _ _ _ _ _ hlo h1]
      exact writeWord_sparse_read_back mem 64 next
  · have hn : (UInt256.ofNat heap).toNat = heap := ulit_toNat' heap hb
    change memLoad (UInt256.ofNat heap) m4 = UInt256.ofNat len
    rw [memLoad_of_prefix h34 _ (by rw [hn]; exact hlo) (by rw [hn]) (by rw [hn]; exact h2)]
    apply mloadWordValue_of_readWithPadding
    · rw [hn]; omega
    · rw [hn]
      exact writeWord_sparse_read_back m1 heap (UInt256.ofNat len)
  · change m4.readWithPadding (heap+32) len = _
    dsimp only [m4]
    rw [writeWord_read_below_len _ _ _ _ _ (le_refl _) hpayload.1]
    exact hpayload.2

end Benchmarks.EAS.EAS
