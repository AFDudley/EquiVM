import Benchmarks.Morpho.MetaMorphoV1_1.StructReturnMemory
import Benchmarks.Morpho.MetaMorphoV1_1.WordCallMemory

/-! LIBRARY CANDIDATE: memory preservation for fixed-size external call buffers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem wordCallMemory_free {mem : ByteArray} {ptr : Nat} (selector : UInt256)
    (words : List UInt256) (hmem : 96 ≤ mem.size) (hptr : 96 ≤ ptr) :
    memLoad ⟨64⟩ (wordCallMemory mem ptr selector words) = memLoad ⟨64⟩ mem := by
  change memLoad (UInt256.ofNat 64) _ = _
  rw [wordCallMemory, wordSequenceMemory_load_below (read := 64) words
    (by rw [writeWord_sparse_size]; omega) (by omega) (by decide)]
  exact memLoad_write_disjoint mem ptr ⟨64⟩ selector hmem (.inl hptr)

theorem fixedReturnBuffer_capped (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    {cap : Nat} (hcap : cap < UInt256.size) (hout : out.size < UInt256.size) :
    fixedReturnBuffer mem ptr out cap = out.write 0 mem ptr.toNat (min cap out.size) := by
  by_cases hl : cap ≤ out.size
  · rw [fixedReturnBuffer, umin_ofNat_right_toNat_of_ge hcap hl hout, Nat.min_eq_left hl]
  · rw [fixedReturnBuffer, umin_ofNat_right_toNat_of_lt hcap (by omega) hout,
      Nat.min_eq_right (by omega)]

theorem fixedReturnBuffer_prefix {mem out : ByteArray} {ptr : UInt256} {cap : Nat}
    (hcap : cap < UInt256.size) (hout : out.size < UInt256.size) (hin : ptr.toNat ≤ mem.size) :
    MemoryPrefix mem (fixedReturnBuffer mem ptr out cap) ptr.toNat := by
  rw [fixedReturnBuffer_capped _ _ _ hcap hout]
  by_cases hz : min cap out.size = 0
  · rw [hz, byteArray_write_len_zero]
    exact .refl _ _
  · exact copyWindow_prefix _ _ _ _ _ _ hz (by omega) hin (.inl (le_refl _))

theorem fixedReturnBuffer_free {mem out : ByteArray} {ptr : UInt256} {cap : Nat}
    (hcap : cap < UInt256.size) (hout : out.size < UInt256.size)
    (hin : ptr.toNat ≤ mem.size) (hlo : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (fixedReturnBuffer mem ptr out cap) = memLoad ⟨64⟩ mem := by
  rw [fixedReturnBuffer_capped _ _ _ hcap hout]
  by_cases hz : min cap out.size = 0
  · rw [hz, byteArray_write_len_zero]
  · have hm := copyWindow_size out mem 0 ptr.toNat (min cap out.size) hz (by omega) hin
    simp only [memLoad, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
      if_neg (by rw [hm]; omega : ¬ 64 ≥ (out.write 0 mem ptr.toNat (min cap out.size)).size),
      if_neg (by omega : ¬ 64 ≥ mem.size)]
    rw [copyWindow_read_preserved out mem 0 ptr.toNat (min cap out.size) 64
      hz (by omega) hin (by omega) (.inl hlo)]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
