import Benchmarks.Morpho.MetaMorphoV1_1.BytesBuffer

/-! The result pointer array and all byte buffers retained by the multicall loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

structure MulticallMemory (mem : ByteArray) (cursor : UInt256) (results : List ByteArray) : Prop where
  bound : cursor.toNat < 2 ^ 64
  lower : 160 + 32 * results.length ≤ cursor.toNat
  size : 160 + 32 * results.length ≤ mem.size
  free : memLoad ⟨64⟩ mem = cursor
  zero : memLoad ⟨96⟩ mem = ⟨0⟩
  length : memLoad ⟨128⟩ mem = UInt256.ofNat results.length
  data : ∀ j (hj : j < results.length), ∃ p : UInt256,
    (p = ⟨96⟩ ∨ 160 + 32 * results.length ≤ p.toNat) ∧
    p.toNat + 32 + results[j].size ≤ cursor.toNat ∧ results[j].size < 2 ^ 64 ∧
    BytesBuffer mem p results[j] ∧ memLoad (UInt256.ofNat (160 + 32 * j)) mem = p

theorem MulticallMemory.preserve {before after : ByteArray} {free next : UInt256}
    {results : List ByteArray} (h : MulticallMemory before free results)
    (hp : ByteMemoryPrefix before after free.toNat)
    (hn : next.toNat < 2 ^ 64) (hle : free.toNat ≤ next.toNat)
    (hf : memLoad ⟨64⟩ after = next) : MulticallMemory after next results := by
  refine ⟨hn, le_trans h.lower hle, le_trans h.size hp.size, hf, ?_, ?_, ?_⟩
  · have he := hp.words.load_preserved (off := 96) (by decide)
      (by have := h.lower; omega) (by have := h.size; omega) (by decide)
    exact he.trans h.zero
  · have he := hp.words.load_preserved (off := 128) (by decide)
      (by have := h.lower; omega) (by have := h.size; omega) (by decide)
    exact he.trans h.length
  · intro j hj
    obtain ⟨p, hl, he, hb, hbuf, hs⟩ := h.data j hj
    have hlo : 96 ≤ p.toNat := by
      rcases hl with rfl | hl
      · decide
      · omega
    refine ⟨p, hl, le_trans he hle, hb, hbuf.preserve hp hlo he, ?_⟩
    have hr := hp.words.load_preserved (off := 160 + 32 * j) (by omega)
      (by have := h.lower; omega) (by have := h.size; omega)
      (by have := h.lower; have := h.bound; change _ < 2 ^ 256; omega)
    exact hr.trans hs

theorem MulticallMemory.storeResult {mem : ByteArray} {free p : UInt256}
    {results : List ByteArray} {i : Nat} {out : ByteArray}
    (h : MulticallMemory mem free results) (hi : i < results.length)
    (hloc : p = ⟨96⟩ ∨ 160 + 32 * results.length ≤ p.toNat)
    (hend : p.toNat + 32 + out.size ≤ free.toNat) (hlen : out.size < 2 ^ 64)
    (hbuf : BytesBuffer mem p out) :
    MulticallMemory (writeWord mem (160 + 32 * i) p) free (results.set i out) := by
  have hfit : 160 + 32 * results.length < UInt256.size := by
    have := h.lower; have := h.bound; change _ < 2 ^ 256; omega
  have hload (off : Nat) (hlower : 96 ≤ off) (hlo : off + 32 ≤ 160 + 32 * i) (hin : off + 32 ≤ mem.size)
      (hoff : off < UInt256.size) :
      memLoad (UInt256.ofNat off) (writeWord mem (160 + 32 * i) p) =
        memLoad (UInt256.ofNat off) mem := by
    exact (memoryPrefix_sparse_writeWord mem (160 + 32 * i) (160 + 32 * i) p
      (.inl (le_refl _))).load_preserved hlower hlo hin hoff
  have hfree : memLoad ⟨64⟩ (writeWord mem (160 + 32 * i) p) = free := by
    rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
      (by change 96 ≤ mem.size; have := h.size; omega) (.inl (by change 96 ≤ _; omega))]
    exact h.free
  refine ⟨h.bound, by simpa only [List.length_set] using h.lower,
    by rw [writeWord_sparse_size, List.length_set]; have := h.size; omega,
    hfree, ?_, ?_, ?_⟩
  · exact (hload 96 (by decide) (by omega) (by have := h.size; omega) (by decide)).trans h.zero
  · simpa only [List.length_set] using
      (hload 128 (by decide) (by omega) (by have := h.size; omega) (by decide)).trans h.length
  · intro j hj
    have hj' : j < results.length := by simpa only [List.length_set] using hj
    have hdis (q : UInt256) (bytes : ByteArray)
        (hl : q = ⟨96⟩ ∨ 160 + 32 * results.length ≤ q.toNat)
        (hb : BytesBuffer mem q bytes) (hsz : bytes.size < 2 ^ 64) :
        q.toNat + 32 + bytes.size ≤ 160 + 32 * i ∨ 160 + 32 * i + 32 ≤ q.toNat := by
      rcases hl with rfl | hl
      · have hz : bytes.size = 0 := by
          have he := h.zero.symm.trans hb.length
          have hsz : bytes.size < UInt256.size := lt_trans hsz (by decide)
          have he' := congrArg UInt256.toNat he
          rw [UInt256.toNat_ofNat_of_lt hsz] at he'
          exact he'.symm
        exact .inl (by rw [hz]; change 96 + 32 + 0 ≤ _; omega)
      · exact .inr (by omega)
    by_cases he : i = j
    · subst j
      simp only [List.getElem_set_self, List.length_set]
      exact ⟨p, hloc, hend, hlen, hbuf.writeWord _ _ (hdis p out hloc hbuf hlen),
        memLoad_write_same _ _ _ _ (UInt256.toNat_ofNat_of_lt (by omega))⟩
    · simp only [List.getElem_set_ne he, List.length_set]
      obtain ⟨q, hl, hb, hs, hbuffer, hslot⟩ := h.data j hj'
      refine ⟨q, hl, hb, hs, hbuffer.writeWord _ _ (hdis q _ hl hbuffer hs), ?_⟩
      rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
        (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; have := h.size; omega)
        (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)]
      exact hslot

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
