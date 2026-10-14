import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayEncodeStep

/-! Read back the complete offset table and dynamic payload sequence. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem bytesArrayEncodeMemory_read {mem : ByteArray} {slot head tail origin limit : Nat}
    {bs : List ByteArray} (h : BytesArraySources mem slot limit bs)
    (hb : limit < UInt256.size) (hh : limit ≤ head) (ht : head + 32 * bs.length ≤ tail)
    (ho : origin + 64 ≤ tail) (hinit : bs = [] → tail ≤ mem.size) :
    tail + (bytesArrayTails bs).size ≤ (bytesArrayEncodeMemory mem slot head tail origin bs).size ∧
    (bytesArrayEncodeMemory mem slot head tail origin bs).readWithPadding head (32 * bs.length) =
      bytesArrayHeads (tail - origin - 64) bs ∧
    (bytesArrayEncodeMemory mem slot head tail origin bs).readWithPadding tail
      (bytesArrayTails bs).size = bytesArrayTails bs := by
  induction bs generalizing mem slot head tail with
  | nil =>
      refine ⟨?_, ?_, ?_⟩
      · simpa only [bytesArrayTails, bytesArrayEncodeMemory, ByteArray.size_empty, Nat.add_zero]
          using hinit rfl
      · exact byteArray_readWithPadding_zero _ _
      · exact byteArray_readWithPadding_zero _ _
  | cons b bs ih =>
      have ht' : head + 32 ≤ tail := by simp only [List.length_cons] at ht; omega
      have hp := bytesArrayEncodeStep_prefix h hh ht' (origin := origin)
      have hs := (h.preserve hb (hp.mono hh)).tail
      obtain ⟨hsize, hhead, htail⟩ := bytesArrayEncodeStep_facts h hh ht' (origin := origin)
      have hnext : head + 32 + 32 * bs.length ≤ tail + 32 + paddedSize b.size := by
        simp only [List.length_cons] at ht; omega
      obtain ⟨hend, hheads, htails⟩ := ih (head := head + 32)
        (tail := tail + 32 + paddedSize b.size) hs (by omega) hnext (by omega) (fun _ ↦ hsize)
      have hpre := bytesArrayEncodeMemory_prefix hs hb (by omega) hnext (origin := origin)
      have hhread : (bytesArrayEncodeMemory
          (bytesArrayEncodeStep mem slot head tail origin b) (slot + 32) (head + 32)
          (tail + 32 + paddedSize b.size) origin bs).readWithPadding head 32 =
            (UInt256.ofNat (tail - origin - 64)).toByteArray := by
        rw [hpre.read head 32 (by have := h.lower; have := h.bound; omega) (by omega)
          (by omega), hhead]
      have htread : (bytesArrayEncodeMemory
          (bytesArrayEncodeStep mem slot head tail origin b) (slot + 32) (head + 32)
          (tail + 32 + paddedSize b.size) origin bs).readWithPadding tail
            (32 + paddedSize b.size) = stringPayloadBytes b := by
        rw [bytesArrayEncodeMemory_gap hs hb (by omega) hnext tail (32 + paddedSize b.size)
          (by have := h.lower; have := h.bound; omega)
          (by simp only [List.length_cons] at ht; omega) (by omega) (by omega), htail]
      simp only [bytesArrayEncodeMemory, bytesArrayTails_size_cons, List.length_cons]
      refine ⟨by omega, ?_, ?_⟩
      · rw [show 32 * (bs.length + 1) = 32 + 32 * bs.length by omega,
          readWithPadding_split _ _ _ _ (by omega), hhread, hheads, bytesArrayHeads]
        rw [show tail + 32 + paddedSize b.size - origin - 64 =
          tail - origin - 64 + 32 + paddedSize b.size by omega]
      · rw [readWithPadding_split _ _ _ _ (by omega), htread,
          show tail + (32 + paddedSize b.size) = tail + 32 + paddedSize b.size by omega, htails]
        rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
