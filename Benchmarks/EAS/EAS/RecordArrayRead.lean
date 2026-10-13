import Benchmarks.EAS.EAS.RecordArrayLoopViews
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem RecordArrayLoopView.final_covered {before mem : ByteArray} {base : UInt256}
    {ats : List AttestationRecord} {limit : Nat} (h : RecordArrayLoopView before mem base ats limit ats.length) :
    recordArrayTail base ats ats.length ≤ mem.size := by
  rcases h.bodiesCovered with hz | hcovered
  · have hc := h.headsCovered
    simp only [hz, recordArrayTail, recordArrayHead, attestationArrayOffset, attestationArrayBodies,
      List.take_zero, List.map_nil, dynamicBodies, ByteArray.size_empty, Nat.mul_zero, Nat.add_zero] at hc ⊢
    exact hc
  · exact hcovered

theorem RecordArrayLoopView.record_read {before mem : ByteArray} {base : UInt256}
    {ats : List AttestationRecord} {limit : Nat} (h : RecordArrayLoopView before mem base ats limit ats.length) :
    mem.readWithPadding (base.toNat+64) (attestationArrayEncoding ats).size = attestationArrayEncoding ats := by
  have hc := h.final_covered
  have hl : (wordBytes (attestationArrayHeads ats ats.length)).size = 32*ats.length := by
    rw [wordBytes_size, attestationArrayHeads_length ats ats.length (le_refl _)]
  have hhead : mem.readWithPadding (base.toNat+64+32) (wordBytes (attestationArrayHeads ats ats.length)).size =
      wordBytes (attestationArrayHeads ats ats.length) := by
    rw [hl]
    simpa only [recordArrayHead, Nat.mul_zero, Nat.add_zero, show base.toNat+64+32=base.toNat+96 by omega] using h.heads
  have hh := readWithPadding_concat mem (base.toNat+64) (UInt256.ofNat ats.length).toByteArray
    (wordBytes (attestationArrayHeads ats ats.length))
    (by rw [toByteArray_size]; exact h.lengthWord)
    (by rw [toByteArray_size]; exact hhead)
    (by rw [toByteArray_size, hl]; unfold recordArrayTail attestationArrayOffset at hc; omega)
  have hh' : mem.readWithPadding (base.toNat+64) (wordBytes (UInt256.ofNat ats.length::attestationArrayHeads ats ats.length)).size =
      wordBytes (UInt256.ofNat ats.length::attestationArrayHeads ats ats.length) := by
    simpa only [wordBytes, ByteArray.size_append] using hh
  have hb : mem.readWithPadding ((base.toNat+64)+(wordBytes (UInt256.ofNat ats.length::attestationArrayHeads ats ats.length)).size)
      (attestationArrayBodies ats ats.length).size = attestationArrayBodies ats ats.length := by
    simp only [wordBytes, ByteArray.size_append, toByteArray_size, hl]
    rw [show base.toNat+64+(32+32*ats.length)=recordArrayHead base ats.length by unfold recordArrayHead; omega]
    exact h.bodies
  have hr := readWithPadding_concat mem (base.toNat+64)
    (wordBytes (UInt256.ofNat ats.length::attestationArrayHeads ats ats.length))
    (attestationArrayBodies ats ats.length) hh' hb (by
      simp only [wordBytes, ByteArray.size_append, toByteArray_size, hl]
      unfold recordArrayTail attestationArrayOffset at hc
      omega)
  simpa only [attestationArrayEncoding, ByteArray.size_append] using hr

end Benchmarks.EAS.EAS
