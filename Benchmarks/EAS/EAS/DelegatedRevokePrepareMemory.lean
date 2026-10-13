import Benchmarks.EAS.EAS.DelegatedRevokeMemory
import Benchmarks.EAS.EAS.AttestPublicMemory
import Benchmarks.EAS.EAS.RecordUID
import Benchmarks.EAS.EAS.SignatureDecode
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: load the word just written to an arbitrary bounded offset.
theorem memLoad_write_at (mem : ByteArray) (off : Nat) (w : UInt256) (ho : off < UInt256.size) :
    memLoad (UInt256.ofNat off) (Reasoning.Theory.writeWord mem off w) = w := by
  apply mloadWordValue_of_readWithPadding
  · rw [ulit_toNat' _ ho,writeWord_sparse_size]; omega
  · rw [ulit_toNat' _ ho]; exact writeWord_sparse_read_back _ _ _

def delegatedRevokeSchemaMemory (cd : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (Reasoning.Theory.writeWord attestPublicInitialMemory 64 (UInt256.ofNat 352)) 224 (calldataWord cd 4)
def delegatedRevokeDataMemory (cd : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (Reasoning.Theory.writeWord
    (Reasoning.Theory.writeWord (delegatedRevokeSchemaMemory cd) 64 (UInt256.ofNat 416))
      352 (calldataWord cd 36)) 384 (calldataWord cd 68)
def delegatedRevokeAllocatedMemory (cd : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (Reasoning.Theory.writeWord (delegatedRevokeDataMemory cd) 256 (UInt256.ofNat 352))
    64 (UInt256.ofNat 512)
def delegatedRevokeSignatureMemory (cd : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord
    (Reasoning.Theory.writeWord (delegatedRevokeAllocatedMemory cd) 416 (calldataWord cd 100))
      448 (calldataWord cd 132)) 480 (calldataWord cd 164)) 288 (UInt256.ofNat 416)
def delegatedRevokeInputMemory (cd : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (delegatedRevokeSignatureMemory cd) 320 (calldataWord cd 196)

theorem delegatedRevokeSchemaMemory_free (cd : ByteArray) :
    memLoad (UInt256.ofNat 64) (delegatedRevokeSchemaMemory cd) = UInt256.ofNat 352 := by
  unfold delegatedRevokeSchemaMemory
  rw [memLoad_write_below _ _ _ _ (by decide) (by rw [writeWord_sparse_size]; change 96 ≤ _; omega),memLoad_write_at _ _ _ (by decide)]

theorem delegatedRevokeDataMemory_free (cd : ByteArray) :
    memLoad (UInt256.ofNat 64) (delegatedRevokeDataMemory cd) = UInt256.ofNat 416 := by
  unfold delegatedRevokeDataMemory
  simp (disch := (first | decide | (simp (disch := decide) only [delegatedRevokeSchemaMemory,writeWord_sparse_size,ulit_toNat']; omega))) only [memLoad_write_below,memLoad_write_at]

theorem delegatedRevokeInputMemory_view (cd : ByteArray) (hv : signatureClean (signatureRecord cd 100))
    (ha : (calldataWord cd 196).toNat < EVM.addressModulus) :
    DelegatedRevokeMemoryView (delegatedRevokeInputMemory cd) (UInt256.ofNat 224) (UInt256.ofNat 352)
      (UInt256.ofNat 416)
      ⟨calldataWord cd 4,revocationDataRecord cd 36,signatureRecord cd 100,AccountAddress.ofNat (calldataWord cd 196).toNat⟩ 512 ∧
    memLoad (UInt256.ofNat 64) (delegatedRevokeInputMemory cd) = UInt256.ofNat 512 := by
  have hsize : (delegatedRevokeInputMemory cd).size = 512 := by
    simp only [delegatedRevokeInputMemory,delegatedRevokeSignatureMemory,delegatedRevokeAllocatedMemory,
      delegatedRevokeDataMemory,delegatedRevokeSchemaMemory,attestPublicInitialMemory,writeWord_sparse_size]
    rfl
  have hload (off : Nat) (ho : off ∈ [64,224,256,288,320,352,384,416,448,480]) :
      memLoad (UInt256.ofNat off) (delegatedRevokeInputMemory cd) =
        if off = 64 then UInt256.ofNat 512 else if off = 224 then calldataWord cd 4 else
        if off = 256 then UInt256.ofNat 352 else if off = 288 then UInt256.ofNat 416 else
        if off = 320 then calldataWord cd 196 else if off = 352 then calldataWord cd 36 else
        if off = 384 then calldataWord cd 68 else if off = 416 then calldataWord cd 100 else
        if off = 448 then calldataWord cd 132 else calldataWord cd 164 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with h|h|h|h|h|h|h|h|h|h <;> subst off <;>
      simp (disch := (first | decide | (simp (disch := decide) only [delegatedRevokeSchemaMemory,writeWord_sparse_size,ulit_toNat']; omega))) only [
        delegatedRevokeInputMemory,delegatedRevokeSignatureMemory,delegatedRevokeAllocatedMemory,
        delegatedRevokeDataMemory,delegatedRevokeSchemaMemory,memLoad_write_below,memLoad_write_above,memLoad_write_at] <;>
      norm_num
  refine ⟨⟨by decide,by rw [hsize]; decide,by decide,?_,?_,?_,?_,?_,by decide,?_,by decide⟩,?_⟩
  · exact hload 224 (by simp)
  · exact hload 256 (by simp)
  · exact hload 288 (by simp)
  · have hw := hload 320 (by simp)
    simp only [show (320 : Nat) ≠ 64 by decide,show (320 : Nat) ≠ 224 by decide,
      show (320 : Nat) ≠ 256 by decide,show (320 : Nat) ≠ 288 by decide,if_false,if_true] at hw
    change UInt256.land (memLoad (UInt256.ofNat 320) _) solcAddrMask = _
    rw [hw,solcAddrMask_clean ha]
    exact (addressWord_eq_ofNat_address ha).symm
  · refine ⟨by decide,by rw [hsize]; decide,?_,?_⟩
    · exact hload 352 (by simp)
    · exact hload 384 (by simp)
  · refine ⟨by decide,by rw [hsize]; decide,?_,?_,?_⟩
    · change UInt256.land (memLoad (UInt256.ofNat 416) _) (UInt256.ofNat 255) = _
      rw [hload 416 (by simp)]
      exact hv.symm
    · exact hload 448 (by simp)
    · exact hload 480 (by simp)
  · exact hload 64 (by simp)


theorem delegatedRevokeInputMemory_zero (cd : ByteArray) :
    memLoad (UInt256.ofNat 96) (delegatedRevokeInputMemory cd) = ⟨0⟩ := by
  have hm : memLoad (UInt256.ofNat 96) (delegatedRevokeSchemaMemory cd) = ⟨0⟩ := by
    change memLoad (UInt256.ofNat 96)
      (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord attestPublicInitialMemory 64 (UInt256.ofNat 352)) 224 (calldataWord cd 4)) = ⟨0⟩
    apply mloadWordValue_of_readWithPadding
    · rw [writeWord_sparse_size]; change 96 < _; omega
    · change (Reasoning.Theory.writeWord _ 224 (calldataWord cd 4)).readWithPadding 96 32 = _
      rw [writeWord_sparse_eq _ _ _ (by native_decide)]
      rw [readWithPadding_eq_extract _ _ (by
        simp only [ByteArray.size_append,ByteArray_zeroes_size,toByteArray_size]
        native_decide)]
      rw [extract_append_left _ _ _ _ (by native_decide)]
      native_decide
  simp (disch := (first | decide | (simp (disch := decide) only [delegatedRevokeSchemaMemory,writeWord_sparse_size,ulit_toNat']; omega))) only [
    delegatedRevokeInputMemory,delegatedRevokeSignatureMemory,delegatedRevokeAllocatedMemory,
    delegatedRevokeDataMemory,memLoad_write_below,memLoad_write_above]
  exact hm

end Benchmarks.EAS.EAS
