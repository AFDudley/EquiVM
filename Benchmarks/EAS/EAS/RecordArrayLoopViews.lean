import Benchmarks.EAS.EAS.RecordArrayMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def recordArrayHead (base : UInt256) (i : Nat) : Nat := base.toNat+96+32*i

def recordArrayTail (base : UInt256) (ats : List AttestationRecord) (i : Nat) : Nat :=
  base.toNat+96+attestationArrayOffset ats i

structure RecordArrayLoopView (before mem : ByteArray) (base : UInt256) (ats : List AttestationRecord) (limit i : Nat) : Prop where
  index : i ≤ ats.length
  front : MemoryPrefix before mem limit
  headsCovered : recordArrayHead base i ≤ mem.size
  heads : mem.readWithPadding (recordArrayHead base 0) (32*i) = wordBytes (attestationArrayHeads ats i)
  bodiesCovered : i=0 ∨ recordArrayTail base ats i ≤ mem.size
  baseOffset : mem.readWithPadding base.toNat 32 = (UInt256.ofNat 64).toByteArray
  lengthWord : mem.readWithPadding (base.toNat+64) 32 = (UInt256.ofNat ats.length).toByteArray
  bodies : mem.readWithPadding (recordArrayHead base ats.length) (attestationArrayBodies ats i).size = attestationArrayBodies ats i

theorem recordArrayTail_step (base : UInt256) (ats : List AttestationRecord) (i : Nat) (hi : i < ats.length) :
    recordArrayTail base ats (i+1) = recordArrayTail base ats i+ats[i].encoding.size := by
  simp only [recordArrayTail, (attestationArray_step ats i hi).2.2, Nat.add_assoc]

theorem recordArrayHead_step (base : UInt256) (i : Nat) :
    recordArrayHead base (i+1) = recordArrayHead base i+32 := by unfold recordArrayHead; omega

theorem recordArrayTail_start (base : UInt256) (ats : List AttestationRecord) (i : Nat) :
    recordArrayTail base ats i = recordArrayHead base ats.length+(attestationArrayBodies ats i).size := by
  unfold recordArrayTail recordArrayHead attestationArrayOffset
  omega

theorem recordArrayLoopStep_view {before mem after : ByteArray} {base : UInt256}
    {ats : List AttestationRecord} {limit i : Nat}
    (h : RecordArrayLoopView before mem base ats limit i) (hi : i < ats.length)
    (hlo : 96 ≤ limit) (hbase : limit ≤ base.toNat)
    (hbound : base.toNat+128+attestationArrayOffset ats ats.length < UInt256.size)
    (hv : RecordArrayStepView mem after (UInt256.ofNat (recordArrayHead base i)) base
      (UInt256.ofNat (recordArrayTail base ats i)) ats[i]) :
    RecordArrayLoopView before after base ats limit (i+1) := by
  have ho := attestationArrayOffset_le ats i
  have hon := attestationArrayOffset_le ats (i+1)
  have hs := attestationArray_step ats i hi
  have he := ats[i].encoding_size
  have hh : recordArrayHead base i < UInt256.size := by
    unfold recordArrayHead attestationArrayOffset at *
    omega
  have ht : recordArrayTail base ats i < UInt256.size := by unfold recordArrayTail; omega
  have hhn : (UInt256.ofNat (recordArrayHead base i)).toNat = recordArrayHead base i := ulit_toNat' _ hh
  have htn : (UInt256.ofNat (recordArrayTail base ats i)).toNat = recordArrayTail base ats i := ulit_toNat' _ ht
  have hc : recordArrayTail base ats (i+1) ≤ after.size := by
    rw [recordArrayTail_step base ats i hi]
    simpa only [htn] using hv.covered
  have hhp : MemoryPrefix mem after (recordArrayHead base i) := by simpa only [hhn] using hv.front
  have hheadlim : limit ≤ recordArrayHead base i := by unfold recordArrayHead; omega
  have htailhead : recordArrayHead base (i+1) ≤ recordArrayTail base ats (i+1) := by
    unfold recordArrayHead recordArrayTail attestationArrayOffset
    omega
  refine ⟨by omega, h.front.trans (hhp.mono hheadlim), le_trans htailhead hc, ?_, Or.inr hc, ?_, ?_, ?_⟩
  · have hhead : after.readWithPadding (recordArrayHead base i) 32 =
        (UInt256.ofNat (attestationArrayOffset ats i)).toByteArray := by
      have hx : recordArrayOffsetWord base (UInt256.ofNat (recordArrayTail base ats i)) =
          UInt256.ofNat (attestationArrayOffset ats i) := by
        rw [recordArrayOffsetWord_eq base _ (by rw [htn]; unfold recordArrayTail; omega), htn]
        congr 1
        unfold recordArrayTail
        omega
      simpa only [hhn, hx] using hv.headRead
    have hold : after.readWithPadding (recordArrayHead base 0) (wordBytes (attestationArrayHeads ats i)).size =
        wordBytes (attestationArrayHeads ats i) := by
      rw [wordBytes_size, attestationArrayHeads_length ats i (by omega),
        memoryPrefix_read_words hhp (recordArrayHead base 0) i
          (by unfold recordArrayHead; omega) (by unfold recordArrayHead; omega)
          (by have := h.headsCovered; unfold recordArrayHead at *; omega)
          (by unfold recordArrayHead at *; omega)]
      exact h.heads
    have hn : recordArrayHead base 0+(wordBytes (attestationArrayHeads ats i)).size = recordArrayHead base i := by
      rw [wordBytes_size, attestationArrayHeads_length ats i (by omega)]
      unfold recordArrayHead
      omega
    have hr := readWithPadding_concat after (recordArrayHead base 0) (wordBytes (attestationArrayHeads ats i))
      (UInt256.ofNat (attestationArrayOffset ats i)).toByteArray hold
      (by rw [hn, toByteArray_size]; exact hhead)
      (by rw [hn, toByteArray_size]; simpa only [recordArrayHead_step] using le_trans htailhead hc)
    rw [wordBytes_size, attestationArrayHeads_length ats i (by omega), toByteArray_size] at hr
    rw [hs.2.1, wordBytes_append]
    simpa only [wordBytes, ByteArray.append_empty, show 32*(i+1)=32*i+32 by omega] using hr
  · rw [memoryPrefix_read_words hhp base.toNat 1 (by omega)
      (by unfold recordArrayHead; omega)
      (by have := h.headsCovered; unfold recordArrayHead at *; omega) (by unfold recordArrayHead at hh; omega)]
    exact h.baseOffset
  · rw [memoryPrefix_read_words hhp (base.toNat+64) 1 (by omega)
      (by unfold recordArrayHead; omega)
      (by have := h.headsCovered; unfold recordArrayHead at *; omega) (by unfold recordArrayHead at hh; omega)]
    exact h.lengthWord
  · have hold : after.readWithPadding (recordArrayHead base ats.length) (attestationArrayBodies ats i).size =
        attestationArrayBodies ats i := by
      by_cases hiz : i=0
      · subst i
        simp only [attestationArrayBodies, List.take_zero, List.map_nil, dynamicBodies, ByteArray.size_empty,
          byteArray_readWithPadding_zero]
      · have hm := attestationArrayBodies_aligned ats i
        have hn : 32*((attestationArrayBodies ats i).size/32)=(attestationArrayBodies ats i).size := by omega
        have hg := hv.gap (recordArrayHead base ats.length) ((attestationArrayBodies ats i).size/32)
          (by rw [hhn]; unfold recordArrayHead; omega)
          (by rw [hn, htn, recordArrayTail_start])
          (by rw [hn, ← recordArrayTail_start]; exact h.bodiesCovered.resolve_left hiz)
        rw [hn] at hg
        exact hg.trans h.bodies
    have hn : recordArrayHead base ats.length+(attestationArrayBodies ats i).size = recordArrayTail base ats i :=
      (recordArrayTail_start base ats i).symm
    have hnew : after.readWithPadding (recordArrayHead base ats.length+(attestationArrayBodies ats i).size) ats[i].encoding.size = ats[i].encoding := by
      rw [hn]
      simpa only [htn] using hv.recordRead
    have hr := readWithPadding_concat after (recordArrayHead base ats.length) (attestationArrayBodies ats i) ats[i].encoding
      hold hnew (by rw [hn, ← recordArrayTail_step base ats i hi]; exact hc)
    rw [hs.1, ByteArray.size_append]
    exact hr

end Benchmarks.EAS.EAS
