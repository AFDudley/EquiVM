import Benchmarks.Morpho.MetaMorphoV1_1.MulticallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.StringEncoderBytePrefix
import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayReturnABI

/-! Source buffers and preservation facts for encoding a bytes-array result. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: a pointer table and its byte buffers below an allocation boundary.
structure BytesArraySources (mem : ByteArray) (slot limit : Nat) (bs : List ByteArray) : Prop where
  lower : 96 ≤ slot
  bound : slot + 32 * bs.length ≤ limit
  size : slot + 32 * bs.length ≤ mem.size
  data : ∀ j (hj : j < bs.length), ∃ p : UInt256,
    96 ≤ p.toNat ∧ p.toNat + 32 + bs[j].size ≤ limit ∧ bs[j].size < 2 ^ 64 ∧
    BytesBuffer mem p bs[j] ∧ memLoad (UInt256.ofNat (slot + 32 * j)) mem = p

theorem MulticallMemory.sources {mem : ByteArray} {free : UInt256} {bs : List ByteArray}
    (h : MulticallMemory mem free bs) : BytesArraySources mem 160 free.toNat bs := by
  refine ⟨by decide, h.lower, h.size, ?_⟩
  intro j hj
  obtain ⟨p, hlo, hend, hs, hbuf, hslot⟩ := h.data j hj
  refine ⟨p, ?_, hend, hs, hbuf, hslot⟩
  rcases hlo with rfl | hlo
  · decide
  · omega

theorem BytesArraySources.preserve {before after : ByteArray} {slot limit : Nat}
    {bs : List ByteArray} (h : BytesArraySources before slot limit bs)
    (hb : limit < UInt256.size) (hp : ByteMemoryPrefix before after limit) :
    BytesArraySources after slot limit bs := by
  refine ⟨h.lower, h.bound, le_trans h.size hp.size, ?_⟩
  intro j hj
  obtain ⟨p, hlo, hend, hs, hbuf, hslot⟩ := h.data j hj
  refine ⟨p, hlo, hend, hs, hbuf.preserve hp hlo hend, ?_⟩
  exact (hp.words.load_preserved (by have := h.lower; omega)
    (by have := h.bound; omega) (by have := h.size; omega)
    (by have := h.bound; omega)).trans hslot

theorem BytesArraySources.tail {mem : ByteArray} {slot limit : Nat}
    {b : ByteArray} {bs : List ByteArray} (h : BytesArraySources mem slot limit (b :: bs)) :
    BytesArraySources mem (slot + 32) limit bs := by
  refine ⟨by have := h.lower; omega, by have he := h.bound; simp only [List.length_cons] at he; omega,
    by have he := h.size; simp only [List.length_cons] at he; omega, ?_⟩
  intro j hj
  have hh := h.data (j + 1) (by simp only [List.length_cons]; omega)
  simpa only [List.getElem_cons_succ, show slot + 32 * (j + 1) = slot + 32 + 32 * j by omega]
    using hh

def bytesArrayEncodeStep (mem : ByteArray) (slot head tail origin : Nat) (b : ByteArray) : ByteArray :=
  let mid := writeWord mem head (UInt256.ofNat (tail - origin - 64))
  stringPayloadMemory mid ((memLoad (UInt256.ofNat slot) mem).toNat + 32)
    tail (UInt256.ofNat b.size)

theorem bytesArrayEncodeStep_prefix {mem : ByteArray} {slot head tail origin limit : Nat}
    {b : ByteArray} {bs : List ByteArray}
    (h : BytesArraySources mem slot limit (b :: bs)) (hh : limit ≤ head)
    (ht : head + 32 ≤ tail) :
    ByteMemoryPrefix mem (bytesArrayEncodeStep mem slot head tail origin b) head := by
  obtain ⟨p, hlo, hend, hs, hbuf, hslot⟩ := h.data 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at hslot hbuf hs
  have hbs : b.size < UInt256.size := lt_trans hs (by decide)
  unfold bytesArrayEncodeStep
  rw [hslot]
  exact (byteMemoryPrefix_writeWord mem head head _ (.inl (le_refl _))).trans
    ((stringPayloadMemory_bytePrefix _ _ _ _
      (by rw [UInt256.toNat_ofNat_of_lt hbs, writeWord_sparse_size]; have := hbuf.size; omega)).mono
      (by omega))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
