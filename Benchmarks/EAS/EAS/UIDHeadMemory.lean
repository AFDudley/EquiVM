import Benchmarks.EAS.EAS.GetUIDExpr
import Benchmarks.EAS.EAS.PackedShift
import Benchmarks.EAS.EAS.PackedMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def uidFirstMemory (mem : ByteArray) (off : Nat) (a : AttestationRecord) : ByteArray :=
  Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem off a.schema) (off+32)
    (UInt256.shiftLeft (UInt256.ofNat a.recipient.val) (UInt256.ofNat 96))

def uidHeadMemory (mem : ByteArray) (off : Nat) (a : AttestationRecord) : ByteArray :=
  let m1 := uidFirstMemory mem off a
  let m2 := Reasoning.Theory.writeWord m1 (off+52) (UInt256.shiftLeft (UInt256.ofNat a.attester.val) (UInt256.ofNat 96))
  let m3 := Reasoning.Theory.writeWord m2 (off+72) (UInt256.shiftLeft a.time (UInt256.ofNat 192))
  let m4 := Reasoning.Theory.writeWord m3 (off+80) (UInt256.shiftLeft a.expirationTime (UInt256.ofNat 192))
  let m5 := Reasoning.Theory.writeWord m4 (off+88) (UInt256.shiftLeft a.revocable.toUInt256 (UInt256.ofNat 248))
  Reasoning.Theory.writeWord m5 (off+89) a.refUID

def uidHeadBytes (a : AttestationRecord) : ByteArray :=
  ⟨(EVM.Word.toBytesBE a.schema ++
    (EVM.Word.toBytesBE (UInt256.ofNat a.recipient.val)).drop 12 ++
    (EVM.Word.toBytesBE (UInt256.ofNat a.attester.val)).drop 12 ++
    (EVM.Word.toBytesBE a.time).drop 24 ++ (EVM.Word.toBytesBE a.expirationTime).drop 24 ++
    [if a.revocable then (1 : UInt8) else 0] ++ EVM.Word.toBytesBE a.refUID).toArray⟩

theorem uidHeadMemory_read (mem : ByteArray) (off : Nat) (a : AttestationRecord) :
    (uidHeadMemory mem off a).readWithPadding off 121 = uidHeadBytes a := by
  unfold uidHeadMemory uidFirstMemory
  rw [writeWord_append_read _ off 89 32 _ (by simp only [writeWord_sparse_size]; omega) (by decide) (by decide),
    writeWord_append_read _ off 88 1 _ (by simp only [writeWord_sparse_size]; omega) (by decide) (by decide),
    writeWord_append_read _ off 80 8 _ (by simp only [writeWord_sparse_size]; omega) (by decide) (by decide),
    writeWord_append_read _ off 72 8 _ (by simp only [writeWord_sparse_size]; omega) (by decide) (by decide),
    writeWord_append_read _ off 52 20 _ (by simp only [writeWord_sparse_size]; omega) (by decide) (by decide),
    writeWord_append_read _ off 32 20 _ (by simp only [writeWord_sparse_size]; omega) (by decide) (by decide),
    writeWord_sparse_read_back]
  have hf (w : UInt256) : w.toByteArray.extract 0 32 = w.toByteArray := by
    rw [← toByteArray_size w]
    exact byteArray_extract_self _
  rw [hf]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  have hr := shiftLeft_bytes_prefix (UInt256.ofNat a.recipient.val) 12 (by decide)
  have ha := shiftLeft_bytes_prefix (UInt256.ofNat a.attester.val) 12 (by decide)
  have ht := shiftLeft_bytes_prefix a.time 24 (by decide)
  have he := shiftLeft_bytes_prefix a.expirationTime 24 (by decide)
  have hb : ((UInt256.shiftLeft a.revocable.toUInt256 (UInt256.ofNat 248)).toByteArray.extract 0 1).toList =
      [if a.revocable then (1 : UInt8) else 0] := by cases a.revocable <;> decide +kernel
  simp only [Nat.reduceMul,Nat.reduceSub] at hr ha ht he
  simp only [byteArray_toList_eq,ByteArray.data_append,Array.toList_append] at hr ha ht he hb ⊢
  rw [hr,ha,ht,he,hb]
  have hw (w : UInt256) : w.toByteArray.data.toList = EVM.Word.toBytesBE w := by
    simpa only [byteArray_toList_eq] using (word_toBytesBE_eq_toByteArray_toList w).symm
  simp only [hw,uidHeadBytes,List.toList_toArray]

theorem uidHeadMemory_prefix (mem : ByteArray) (off limit : Nat) (a : AttestationRecord) (h : limit ≤ off) :
    MemoryPrefix mem (uidHeadMemory mem off a) limit := by
  change MemoryPrefix mem (writeCascade mem [
    (off,a.schema),(off+32,UInt256.shiftLeft (UInt256.ofNat a.recipient.val) (UInt256.ofNat 96)),
    (off+52,UInt256.shiftLeft (UInt256.ofNat a.attester.val) (UInt256.ofNat 96)),
    (off+72,UInt256.shiftLeft a.time (UInt256.ofNat 192)),
    (off+80,UInt256.shiftLeft a.expirationTime (UInt256.ofNat 192)),
    (off+88,UInt256.shiftLeft a.revocable.toUInt256 (UInt256.ofNat 248)),(off+89,a.refUID)]) limit
  apply memoryPrefix_sparse_cascade
  intro w hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact Or.inl (by omega)

theorem uidHeadMemory_covers (mem : ByteArray) (off : Nat) (a : AttestationRecord) :
    off+121 ≤ (uidHeadMemory mem off a).size := by
  simp only [uidHeadMemory,writeWord_sparse_size]
  omega

end Benchmarks.EAS.EAS
