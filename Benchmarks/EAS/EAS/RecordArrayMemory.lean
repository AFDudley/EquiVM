import Benchmarks.EAS.EAS.RecordArrayViews
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure AttestationArrayMemoryView (mem : ByteArray) (array : UInt256) (ats : List AttestationRecord) (limit : Nat) : Prop where
  low : 96 ≤ array.toNat
  span : array.toNat+32+32*ats.length ≤ limit
  covered : array.toNat+32+32*ats.length ≤ mem.size
  length : memLoad array mem = UInt256.ofNat ats.length
  records : ∀ i (hi : i < ats.length), ∃ src dataPtr,
    memLoad (UInt256.ofNat (array.toNat+32+32*i)) mem = src ∧
    AttestationMemoryView mem src dataPtr ats[i] ∧
    src.toNat+320 ≤ limit ∧ dataPtr.toNat+32+32*((ats[i].data.size+31)/32) ≤ limit

theorem AttestationArrayMemoryView.preserve {before after : ByteArray} {array : UInt256}
    {ats : List AttestationRecord} {limit : Nat}
    (h : AttestationArrayMemoryView before array ats limit)
    (hp : MemoryPrefix before after limit) (hlimit : limit < UInt256.size) :
    AttestationArrayMemoryView after array ats limit := by
  refine ⟨h.low, h.span, le_trans h.covered hp.size, ?_, ?_⟩
  · exact (memLoad_of_prefix hp array h.low (by have := h.span; omega) (by have := h.covered; omega)).trans h.length
  · intro i hi
    obtain ⟨src, dataPtr, hs, hv, hsrc, hdata⟩ := h.records i hi
    refine ⟨src, dataPtr, ?_, hv.preserve hp hsrc hdata hlimit, hsrc, hdata⟩
    have hn : (UInt256.ofNat (array.toNat+32+32*i)).toNat = array.toNat+32+32*i :=
      ulit_toNat' _ (by have := h.span; omega)
    exact (memLoad_of_prefix hp _ (by rw [hn]; have := h.low; omega)
      (by rw [hn]; have := h.span; omega) (by rw [hn]; have := h.covered; omega)).trans hs

-- LIBRARY CANDIDATE: adjacent initialized reads concatenate, including empty pieces.
theorem readWithPadding_concat (mem : ByteArray) (off : Nat) (a b : ByteArray)
    (ha : mem.readWithPadding off a.size = a)
    (hb : mem.readWithPadding (off+a.size) b.size = b)
    (hin : off+a.size+b.size ≤ mem.size) :
    mem.readWithPadding off (a.size+b.size) = a++b := by
  by_cases haz : a.size=0
  · have he := byteArray_eq_empty_of_size_eq_zero a haz
    subst a
    simpa only [ByteArray.size_empty, Nat.add_zero, Nat.zero_add, ByteArray.empty_append] using hb
  by_cases hbz : b.size=0
  · have he := byteArray_eq_empty_of_size_eq_zero b hbz
    subst b
    simpa only [ByteArray.size_empty, Nat.add_zero, ByteArray.append_empty] using ha
  rw [byteArray_readWithPadding_split_unbounded mem off a.size b.size (by omega) (by omega) (by omega), ha, hb]

theorem attestationArrayHeads_length (ats : List AttestationRecord) (i : Nat) (hi : i ≤ ats.length) :
    (attestationArrayHeads ats i).length = i := by
  simp only [attestationArrayHeads, dynamicOffsets_length, List.length_map, List.length_take, Nat.min_eq_left hi]

theorem attestationArrayEncoding_size (ats : List AttestationRecord) :
    (attestationArrayEncoding ats).size = 32+attestationArrayOffset ats ats.length := by
  simp only [attestationArrayEncoding, ByteArray.size_append, wordBytes_size, List.length_cons,
    attestationArrayHeads_length ats ats.length (le_refl _), attestationArrayOffset]
  omega

theorem attestationArrayBodies_aligned (ats : List AttestationRecord) (i : Nat) :
    (attestationArrayBodies ats i).size % 32 = 0 := by
  have h : ∀ xs : List AttestationRecord, (dynamicBodies (xs.map AttestationRecord.encoding)).size % 32 = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      simp only [List.map_cons, dynamicBodies, ByteArray.size_append, a.encoding_size]
      omega
  exact h _

theorem attestationArrayBodies_step_size (ats : List AttestationRecord) (i : Nat) (hi : i < ats.length) :
    (attestationArrayBodies ats (i+1)).size = (attestationArrayBodies ats i).size+ats[i].encoding.size := by
  rw [(attestationArray_step ats i hi).1, ByteArray.size_append]

end Benchmarks.EAS.EAS
