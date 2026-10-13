import Benchmarks.EAS.EAS.CopyPreserve
import Benchmarks.EAS.EAS.ReturnWordDecode
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: the complete words of an ABI return buffer held in memory.
structure ReturnMemoryView (mem : ByteArray) (base : Nat) (out : ByteArray) : Prop where
  low : 96 ≤ base
  covered : base+out.size ≤ mem.size
  words : ∀ i, i+32 ≤ out.size → memLoad (UInt256.ofNat (base+i)) mem = calldataWord out i

theorem ReturnMemoryView.preserve {before after out : ByteArray} {base limit : Nat}
    (h : ReturnMemoryView before base out) (hp : MemoryPrefix before after limit)
    (hh : base+out.size ≤ limit) (hb : limit < UInt256.size) :
    ReturnMemoryView after base out := by
  refine ⟨h.low, le_trans h.covered hp.size, ?_⟩
  intro i hi
  have hn : (UInt256.ofNat (base+i)).toNat = base+i := ulit_toNat' _ (by omega)
  rw [memLoad_of_prefix hp _ (by rw [hn]; have := h.low; omega)
    (by rw [hn]; omega) (by rw [hn]; have := h.covered; omega)]
  exact h.words i hi

theorem ReturnMemoryView.copy (mem out : ByteArray) (base : Nat)
    (hlo : 96 ≤ base) (hin : base ≤ mem.size) (hpos : 0 < out.size)
    (hb : base+out.size < UInt256.size) :
    ReturnMemoryView (out.write 0 mem base out.size) base out := by
  have hcovered : base+out.size ≤ (out.write 0 mem base out.size).size := by
    rw [writeBytes_size out mem base (by omega) hin]
    exact Nat.le_max_right _ _
  refine ⟨hlo,hcovered,?_⟩
  intro i hi
  have hn : (UInt256.ofNat (base+i)).toNat = base+i := ulit_toNat' _ (by omega)
  apply mloadWordValue_of_readWithPadding
  · rw [hn]; omega
  · rw [hn, writeReturnCopy_read32 out mem base out.size (base+i) (le_refl _) hin (by omega) (by omega)]
    rw [show base+i-base=i by omega]
    exact (calldataWord_bytes_at hi).symm

theorem returnCopyMemory_prefix (mem out : ByteArray) (base : Nat) (hin : base ≤ mem.size) :
    MemoryPrefix mem (out.write 0 mem base out.size) base := by
  refine ⟨byteArray_write_size_ge_base _ _ _ _ _, ?_⟩
  intro off _ hhi hcovered
  by_cases hz : out.size=0
  · simp only [hz, byteArray_write_len_zero]
  · exact write_read_below_gen_extend out mem base out.size off hz (le_refl _) hin hhi

end Benchmarks.EAS.EAS
