import Benchmarks.Morpho.MetaMorphoV1_1.BytesArraySources

/-! The offset store and dynamic payload copy for one returned byte string. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem bytesArrayEncodeStep_facts {mem : ByteArray} {slot head tail origin limit : Nat}
    {b : ByteArray} {bs : List ByteArray}
    (h : BytesArraySources mem slot limit (b :: bs)) (hh : limit ≤ head)
    (ht : head + 32 ≤ tail) :
    tail + 32 + paddedSize b.size ≤ (bytesArrayEncodeStep mem slot head tail origin b).size ∧
    (bytesArrayEncodeStep mem slot head tail origin b).readWithPadding head 32 =
      (UInt256.ofNat (tail - origin - 64)).toByteArray ∧
    (bytesArrayEncodeStep mem slot head tail origin b).readWithPadding tail
      (32 + paddedSize b.size) = stringPayloadBytes b := by
  obtain ⟨p, hlo, hend, hs, hbuf, hslot⟩ := h.data 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at hslot hbuf hs hend
  have hbs : b.size < UInt256.size := lt_trans hs (by decide)
  let mid := writeWord mem head (UInt256.ofNat (tail - origin - 64))
  have hbm : BytesBuffer mid p b := hbuf.writeWord _ _ (.inl (by omega))
  have hin : p.toNat + 32 + (UInt256.ofNat b.size).toNat ≤ mid.size := by
    rw [UInt256.toNat_ofNat_of_lt hbs]; exact hbm.size
  simp only [bytesArrayEncodeStep, hslot]
  change _ ≤ (stringPayloadMemory mid _ tail _).size ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [stringPayloadMemory_size _ _ _ _ hin, UInt256.toNat_ofNat_of_lt hbs]
    have hp : paddedSize b.size ≤ b.size + 31 := by unfold paddedSize; omega
    omega
  · rw [(stringPayloadMemory_bytePrefix mid _ tail _ hin).read head 32
      (by have := h.lower; have := h.bound; simp only [List.length_cons] at *; omega) ht
      (by dsimp only [mid]; rw [writeWord_sparse_size]; omega)]
    exact writeWord_sparse_read_back _ _ _
  · simpa only [UInt256.toNat_ofNat_of_lt hbs] using
      stringPayloadMemory_read mid b _ tail _ (UInt256.toNat_ofNat_of_lt hbs).symm hin
      (by rw [UInt256.toNat_ofNat_of_lt hbs]; omega)
      (by rw [UInt256.toNat_ofNat_of_lt hbs]; exact hbm.data)

theorem bytesArrayEncodeStep_gap {mem : ByteArray} {slot head tail origin limit : Nat}
    {b : ByteArray} {bs : List ByteArray}
    (h : BytesArraySources mem slot limit (b :: bs)) (hh : limit ≤ head)
    (ht : head + 32 ≤ tail) (read len : Nat) (hlo : 96 ≤ read)
    (ha : head + 32 ≤ read) (hz : read + len ≤ tail) (hin : read + len ≤ mem.size) :
    (bytesArrayEncodeStep mem slot head tail origin b).readWithPadding read len =
      mem.readWithPadding read len := by
  obtain ⟨p, hp, hend, hs, hbuf, hslot⟩ := h.data 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at hslot hbuf hs
  have hbs : b.size < UInt256.size := lt_trans hs (by decide)
  unfold bytesArrayEncodeStep
  rw [hslot, (stringPayloadMemory_bytePrefix _ _ _ _
    (by rw [UInt256.toNat_ofNat_of_lt hbs, writeWord_sparse_size]; have := hbuf.size; omega)).read
      read len hlo hz (by rw [writeWord_sparse_size]; omega)]
  exact writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hin (.inr ha)

def bytesArrayEncodeMemory (mem : ByteArray) (slot head tail origin : Nat) :
    List ByteArray → ByteArray
  | [] => mem
  | b :: bs => bytesArrayEncodeMemory (bytesArrayEncodeStep mem slot head tail origin b)
      (slot + 32) (head + 32) (tail + 32 + paddedSize b.size) origin bs

theorem bytesArrayEncodeMemory_prefix {mem : ByteArray} {slot head tail origin limit : Nat}
    {bs : List ByteArray} (h : BytesArraySources mem slot limit bs)
    (hb : limit < UInt256.size) (hh : limit ≤ head) (ht : head + 32 * bs.length ≤ tail) :
    ByteMemoryPrefix mem (bytesArrayEncodeMemory mem slot head tail origin bs) head := by
  induction bs generalizing mem slot head tail with
  | nil => exact .refl _ _
  | cons b bs ih =>
      have ht' : head + 32 ≤ tail := by simp only [List.length_cons] at ht; omega
      have hp := bytesArrayEncodeStep_prefix h hh ht' (origin := origin)
      have hs := (h.preserve hb (hp.mono hh)).tail
      exact hp.trans ((ih (head := head + 32) (tail := tail + 32 + paddedSize b.size) hs (by omega)
        (by simp only [List.length_cons] at ht; omega)).mono (by omega))

theorem bytesArrayEncodeMemory_gap {mem : ByteArray} {slot head tail origin limit : Nat}
    {bs : List ByteArray} (h : BytesArraySources mem slot limit bs)
    (hb : limit < UInt256.size) (hh : limit ≤ head) (ht : head + 32 * bs.length ≤ tail)
    (read len : Nat) (hlo : 96 ≤ read) (ha : head + 32 * bs.length ≤ read)
    (hz : read + len ≤ tail) (hin : read + len ≤ mem.size) :
    (bytesArrayEncodeMemory mem slot head tail origin bs).readWithPadding read len =
      mem.readWithPadding read len := by
  induction bs generalizing mem slot head tail with
  | nil => rfl
  | cons b bs ih =>
      have ht' : head + 32 ≤ tail := by simp only [List.length_cons] at ht; omega
      have hp := bytesArrayEncodeStep_prefix h hh ht' (origin := origin)
      have hs := (h.preserve hb (hp.mono hh)).tail
      rw [bytesArrayEncodeMemory, ih (head := head + 32) (tail := tail + 32 + paddedSize b.size) hs (by omega)
        (by simp only [List.length_cons] at ht; omega)
        (by simp only [List.length_cons] at ha; omega) (by omega) (le_trans hin hp.size)]
      exact bytesArrayEncodeStep_gap h hh ht' read len hlo
        (by simp only [List.length_cons] at ha; omega) hz hin

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
