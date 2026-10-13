import Benchmarks.EAS.EAS.ConstructorData
import Benchmarks.EAS.EAS.DelegatedRevokePrepareMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def easCtorCode (registry : AccountAddress) : ByteArray := easCreationBytecode ++ (UInt256.ofNat registry.val).toByteArray
def easCtorFreeMemory : ByteArray := writeWord ByteArray.empty 64 (UInt256.ofNat 352)
def easCtorArgAllocated : ByteArray := writeWord easCtorFreeMemory 64 (UInt256.ofNat 384)
def easCtorABIMemory (registry : AccountAddress) : ByteArray := writeWord easCtorArgAllocated 352 (UInt256.ofNat registry.val)
def easCtorVersionAllocated (registry : AccountAddress) : ByteArray := writeWord (easCtorABIMemory registry) 64 (UInt256.ofNat 448)
def easCtorVersionWord : UInt256 := UInt256.shiftLeft (UInt256.ofNat 404166939) (UInt256.ofNat 225)
def easCtorNameWord : UInt256 := UInt256.shiftLeft (UInt256.ofNat 4538707) (UInt256.ofNat 232)
def easCtorVersionMemory (registry : AccountAddress) : ByteArray :=
  writeWord (writeWord (easCtorVersionAllocated registry) 384 (UInt256.ofNat 4)) 416 easCtorVersionWord
def easCtorNameAllocated (registry : AccountAddress) : ByteArray := writeWord (easCtorVersionMemory registry) 64 (UInt256.ofNat 512)
def easCtorStringsMemory (registry : AccountAddress) : ByteArray :=
  writeWord (writeWord (easCtorNameAllocated registry) 448 (UInt256.ofNat 3)) 480 easCtorNameWord

theorem easCtorCreation_size : easCreationBytecode.size = 17674 := by native_decide
theorem easCtorRuntime_size : easBytecode.size = 17208 := by native_decide
theorem easCtorCode_size (registry : AccountAddress) : (easCtorCode registry).size = 17706 := by
  rw [easCtorCode,ByteArray.size_append,easCtorCreation_size,toByteArray_size]
theorem easCtorCode_tail (registry : AccountAddress) :
    (easCtorCode registry).extract 17674 (17674+32) = (UInt256.ofNat registry.val).toByteArray :=
  extract_append_right' _ _ _ _ easCtorCreation_size.symm (by rw [easCtorCreation_size,toByteArray_size])
theorem easCtorCode_runtime (registry : AccountAddress) : (easCtorCode registry).extract 434 (434+17208) = easBytecode := by
  rw [easCtorCode,extract_append_left _ _ _ _ (by rw [easCtorCreation_size]; decide)]
  native_decide
theorem easCtorCode_type (registry : AccountAddress) : (easCtorCode registry).extract 17642 (17642+32) = easCtorType.toByteArray := by
  rw [easCtorCode,extract_append_left _ _ _ _ (by rw [easCtorCreation_size])]
  native_decide

theorem easCtorArgAllocated_size : easCtorArgAllocated.size = 96 := by
  simp only [easCtorArgAllocated,easCtorFreeMemory,writeWord_sparse_size]; rfl
theorem easCtorCode_copyArg (registry : AccountAddress) :
    (easCtorCode registry).write 17674 easCtorArgAllocated 352 32 = easCtorABIMemory registry := by
  rw [write_from_gap_eq _ _ _ _ _ (by decide) (by rw [easCtorCode_size])
    (by rw [easCtorArgAllocated_size]; decide) (by rw [easCtorArgAllocated_size]; exact lt_usize _ (by decide)),easCtorCode_tail,
    easCtorABIMemory,Reasoning.Theory.writeWord,toByteArray_write_eq _ _ _ (by rw [easCtorArgAllocated_size]; decide)
      (by rw [easCtorArgAllocated_size]; exact lt_usize _ (by decide))]
theorem easCtorABIMemory_size (registry : AccountAddress) : (easCtorABIMemory registry).size = 384 := by
  rw [easCtorABIMemory,writeWord_sparse_size,easCtorArgAllocated_size]; rfl
theorem easCtorABIMemory_load (registry : AccountAddress) :
    memLoad (UInt256.ofNat 352) (easCtorABIMemory registry) = UInt256.ofNat registry.val := memLoad_write_at _ _ _ (by decide)
theorem easCtorABIMemory_free (registry : AccountAddress) :
    memLoad (UInt256.ofNat 64) (easCtorABIMemory registry) = UInt256.ofNat 384 := by
  rw [easCtorABIMemory,memLoad_write_below _ _ _ _ (by decide) (by rw [easCtorArgAllocated_size]; decide)]
  exact memLoad_write_at _ _ _ (by decide)
theorem easCtorVersionMemory_size (registry : AccountAddress) : (easCtorVersionMemory registry).size = 448 := by
  simp only [easCtorVersionMemory,easCtorVersionAllocated,writeWord_sparse_size,easCtorABIMemory_size]; rfl
theorem easCtorVersionMemory_free (registry : AccountAddress) :
    memLoad (UInt256.ofNat 64) (easCtorVersionMemory registry) = UInt256.ofNat 448 := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,easCtorABIMemory_size,ulit_toNat']; omega))) only
    [easCtorVersionMemory,easCtorVersionAllocated,memLoad_write_below,memLoad_write_at]
theorem easCtorNameAllocated_free (registry : AccountAddress) :
    memLoad (UInt256.ofNat 64) (easCtorNameAllocated registry) = UInt256.ofNat 512 := memLoad_write_at _ _ _ (by decide)
theorem easCtorStringsMemory_size (registry : AccountAddress) : (easCtorStringsMemory registry).size = 512 := by
  simp only [easCtorStringsMemory,easCtorNameAllocated,writeWord_sparse_size,easCtorVersionMemory_size]; rfl

theorem easCtorStrings_nameLength (registry : AccountAddress) :
    memLoad (UInt256.ofNat 448) (easCtorStringsMemory registry) = UInt256.ofNat 3 := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,ulit_toNat']; omega))) only
    [easCtorStringsMemory,memLoad_write_below,memLoad_write_at]
theorem easCtorStrings_versionLength (registry : AccountAddress) :
    memLoad (UInt256.ofNat 384) (easCtorStringsMemory registry) = UInt256.ofNat 4 := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,easCtorVersionMemory_size,ulit_toNat']; omega))) only
    [easCtorStringsMemory,easCtorNameAllocated,easCtorVersionMemory,easCtorVersionAllocated,memLoad_write_below,memLoad_write_above,memLoad_write_at]
theorem easCtorStrings_free (registry : AccountAddress) :
    memLoad (UInt256.ofNat 64) (easCtorStringsMemory registry) = UInt256.ofNat 512 := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,easCtorVersionMemory_size,ulit_toNat']; omega))) only
    [easCtorStringsMemory,easCtorNameAllocated,memLoad_write_below,memLoad_write_at]
theorem easCtorStrings_name (registry : AccountAddress) : (easCtorStringsMemory registry).readWithPadding 480 3 = "EAS".toUTF8 := by
  rw [easCtorStringsMemory,show 480 = 480+0 by rfl,writeWord_sparse_read_window _ _ _ _ _ (by decide) (by decide) (by decide)]
  native_decide
theorem easCtorStrings_version (registry : AccountAddress) : (easCtorStringsMemory registry).readWithPadding 416 4 = "0.26".toUTF8 := by
  unfold easCtorStringsMemory easCtorNameAllocated
  rw [writeWord_read_preserved_len_of_disjoint (by exact lt_usize _ (by omega)) (.inl ⟨by decide,by simp only [writeWord_sparse_size,easCtorVersionMemory_size]; omega⟩) (by decide) (by decide)]
  rw [writeWord_read_preserved_len_of_disjoint (by exact lt_usize _ (by omega)) (.inl ⟨by decide,by simp only [writeWord_sparse_size,easCtorVersionMemory_size]; omega⟩) (by decide) (by decide)]
  rw [writeWord_read_preserved_len_of_disjoint (by exact lt_usize _ (by omega)) (.inr ⟨by decide,by rw [easCtorVersionMemory_size]; decide⟩) (by decide) (by decide)]
  rw [easCtorVersionMemory,show 416 = 416+0 by rfl,writeWord_sparse_read_window _ _ _ _ _ (by decide) (by decide) (by decide)]
  native_decide

theorem easCtorStrings_nameHash (registry : AccountAddress) :
    keccakWord (UInt256.ofNat 480) (UInt256.ofNat 3) (easCtorStringsMemory registry) = easCtorName := by
  simp only [keccakWord,ulit_toNat' 480 (by decide),ulit_toNat' 3 (by decide),easCtorStrings_name]
  rw [easCtorName,uInt256OfByteArray_eq]
theorem easCtorStrings_versionHash (registry : AccountAddress) :
    keccakWord (UInt256.ofNat 416) (UInt256.ofNat 4) (easCtorStringsMemory registry) = easCtorVersion := by
  simp only [keccakWord,ulit_toNat' 416 (by decide),ulit_toNat' 4 (by decide),easCtorStrings_version]
  rw [easCtorVersion,uInt256OfByteArray_eq]

theorem easCtorCode_copyType (registry : AccountAddress) (mem : ByteArray) (hs : 32 ≤ mem.size) :
    (easCtorCode registry).write 17642 mem 0 32 = writeWord mem 0 easCtorType := by
  rw [write_eq_gen_from _ _ _ _ _ (by decide) (by rw [easCtorCode_size]; decide) (by omega),easCtorCode_type,
    Reasoning.Theory.writeWord,write_eq_gen _ _ _ _ (by decide) (by rw [toByteArray_size]) (by omega),toByteArray_extract0_32]

end Benchmarks.EAS.EAS
