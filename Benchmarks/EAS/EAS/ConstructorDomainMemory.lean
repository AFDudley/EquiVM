import Benchmarks.EAS.EAS.ConstructorMemoryBase
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def easCtorHashMemory (registry : AccountAddress) : ByteArray :=
  writeWord (writeWord (writeWord (easCtorStringsMemory registry) 224 easCtorName) 256 easCtorVersion) 160 (UInt256.ofNat Ethereum.chainId)
def easCtorRestoreMemory (mem : ByteArray) : ByteArray := writeWord (writeWord mem 0 easCtorType) 0 (memLoad (UInt256.ofNat 0) mem)
def easCtorDomainPrefix (registry : AccountAddress) : ByteArray := writeWordSequence (easCtorRestoreMemory (easCtorHashMemory registry)) 544
  [easCtorType,easCtorName,easCtorVersion,UInt256.ofNat Ethereum.chainId]
def easCtorDomainMemory (registry owner : AccountAddress) : ByteArray :=
  writeWord (writeWord (easCtorDomainPrefix registry) 672 (UInt256.ofNat owner.val)) 512 (UInt256.ofNat 160)
def easCtorDomainAllocated (registry owner : AccountAddress) : ByteArray := writeWord (easCtorDomainMemory registry owner) 64 (UInt256.ofNat 704)
def easCtorFinalMemory (registry owner : AccountAddress) : ByteArray :=
  writeWord (easCtorRestoreMemory (writeWord (writeWord (easCtorDomainAllocated registry owner) 128 (easCtorDomain owner))
    192 (UInt256.ofNat owner.val))) 288 easCtorType

theorem easCtorHashMemory_size (registry : AccountAddress) : (easCtorHashMemory registry).size = 512 := by
  simp only [easCtorHashMemory,writeWord_sparse_size,easCtorStringsMemory_size]; rfl
theorem easCtorHashMemory_free (registry : AccountAddress) : memLoad (UInt256.ofNat 64) (easCtorHashMemory registry) = UInt256.ofNat 512 := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,easCtorStringsMemory_size,ulit_toNat']; omega))) only
    [easCtorHashMemory,memLoad_write_below,easCtorStrings_free]
theorem easCtorRestoreMemory_size (mem : ByteArray) (hs : 32 ≤ mem.size) : (easCtorRestoreMemory mem).size = mem.size := by
  simp only [easCtorRestoreMemory,writeWord_sparse_size]; omega
theorem easCtorRestoreMemory_load (mem : ByteArray) (ptr : UInt256) (hlo : 32 ≤ ptr.toNat) (hin : ptr.toNat+32 ≤ mem.size) :
    memLoad ptr (easCtorRestoreMemory mem) = memLoad ptr mem := by
  rw [easCtorRestoreMemory,memLoad_write_above _ _ _ _ hlo (by rw [writeWord_sparse_size]; omega),memLoad_write_above _ _ _ _ hlo hin]
theorem easCtorDomainPrefix_size (registry : AccountAddress) : (easCtorDomainPrefix registry).size = 672 := by
  simp only [easCtorDomainPrefix,writeWordSequence,writeWord_sparse_size,easCtorRestoreMemory,easCtorHashMemory_size]
  rfl
theorem easCtorDomainAllocated_size (registry owner : AccountAddress) : (easCtorDomainAllocated registry owner).size = 704 := by
  simp only [easCtorDomainAllocated,easCtorDomainMemory,writeWord_sparse_size,easCtorDomainPrefix_size]; rfl
theorem easCtorDomainAllocated_length (registry owner : AccountAddress) :
    memLoad (UInt256.ofNat 512) (easCtorDomainAllocated registry owner) = UInt256.ofNat 160 := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,ulit_toNat']; omega))) only
    [easCtorDomainAllocated,easCtorDomainMemory,memLoad_write_above,memLoad_write_at]

theorem easCtorDomainAllocated_payload (registry owner : AccountAddress) :
    (easCtorDomainAllocated registry owner).readWithPadding 544 160 = domainPayload easCtorType easCtorName easCtorVersion owner := by
  unfold easCtorDomainAllocated easCtorDomainMemory
  rw [writeWord_read_preserved_len_of_disjoint (by exact lt_usize _ (by omega)) (.inr ⟨by decide,by simp only [writeWord_sparse_size,easCtorDomainPrefix_size]; decide⟩) (by decide) (by decide)]
  rw [writeWord_read_preserved_len_of_disjoint (by exact lt_usize _ (by omega)) (.inr ⟨by decide,by simp only [writeWord_sparse_size,easCtorDomainPrefix_size]; decide⟩) (by decide) (by decide)]
  change (writeWordSequence (easCtorRestoreMemory (easCtorHashMemory registry)) 544
    [easCtorType,easCtorName,easCtorVersion,UInt256.ofNat Ethereum.chainId,UInt256.ofNat owner.val]).readWithPadding 544
      (32*5) = _
  have hr := writeWordSequence_read (easCtorRestoreMemory (easCtorHashMemory registry)) 544
    [easCtorType,easCtorName,easCtorVersion,UInt256.ofNat Ethereum.chainId,UInt256.ofNat owner.val]
  trans wordBytes [easCtorType,easCtorName,easCtorVersion,UInt256.ofNat Ethereum.chainId,UInt256.ofNat owner.val]
  · exact hr
  exact (domainPayload_wordBytes _ _ _ _).symm

theorem easCtorDomainAllocated_hash (registry owner : AccountAddress) :
    keccakWord (UInt256.ofNat 544) (UInt256.ofNat 160) (easCtorDomainAllocated registry owner) = easCtorDomain owner := by
  simp only [keccakWord,ulit_toNat' 544 (by decide),ulit_toNat' 160 (by decide),easCtorDomainAllocated_payload,easCtorDomain,builtDomainWord,uInt256OfByteArray_eq]

theorem easCtorFinalMemory_size (registry owner : AccountAddress) : (easCtorFinalMemory registry owner).size = 704 := by
  simp only [easCtorFinalMemory,writeWord_sparse_size,easCtorRestoreMemory,easCtorDomainAllocated_size]; rfl

theorem easCtorFinalMemory_free (registry owner : AccountAddress) :
    memLoad (UInt256.ofNat 64) (easCtorFinalMemory registry owner) = UInt256.ofNat 704 := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,easCtorStringsMemory_size,ulit_toNat']; omega))) only
    [easCtorFinalMemory,easCtorRestoreMemory,easCtorDomainAllocated,easCtorDomainMemory,easCtorDomainPrefix,writeWordSequence,
      easCtorHashMemory,memLoad_write_below,memLoad_write_above,memLoad_write_at]

theorem easCtorFinalMemory_domain (registry owner : AccountAddress) :
    memLoad (UInt256.ofNat 128) (easCtorFinalMemory registry owner) = easCtorDomain owner := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,easCtorStringsMemory_size,ulit_toNat']; omega))) only
    [easCtorFinalMemory,easCtorRestoreMemory,easCtorDomainAllocated,easCtorDomainMemory,easCtorDomainPrefix,writeWordSequence,
      easCtorHashMemory,memLoad_write_below,memLoad_write_above,memLoad_write_at]

theorem easCtorFinalMemory_chain (registry owner : AccountAddress) :
    memLoad (UInt256.ofNat 160) (easCtorFinalMemory registry owner) = UInt256.ofNat Ethereum.chainId := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,easCtorStringsMemory_size,ulit_toNat']; omega))) only
    [easCtorFinalMemory,easCtorRestoreMemory,easCtorDomainAllocated,easCtorDomainMemory,easCtorDomainPrefix,writeWordSequence,
      easCtorHashMemory,memLoad_write_below,memLoad_write_above,memLoad_write_at]

theorem easCtorFinalMemory_owner (registry owner : AccountAddress) :
    memLoad (UInt256.ofNat 192) (easCtorFinalMemory registry owner) = UInt256.ofNat owner.val := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,easCtorStringsMemory_size,ulit_toNat']; omega))) only
    [easCtorFinalMemory,easCtorRestoreMemory,easCtorDomainAllocated,easCtorDomainMemory,easCtorDomainPrefix,writeWordSequence,
      easCtorHashMemory,memLoad_write_below,memLoad_write_above,memLoad_write_at]

theorem easCtorFinalMemory_name (registry owner : AccountAddress) :
    memLoad (UInt256.ofNat 224) (easCtorFinalMemory registry owner) = easCtorName := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,easCtorStringsMemory_size,ulit_toNat']; omega))) only
    [easCtorFinalMemory,easCtorRestoreMemory,easCtorDomainAllocated,easCtorDomainMemory,easCtorDomainPrefix,writeWordSequence,
      easCtorHashMemory,memLoad_write_below,memLoad_write_above,memLoad_write_at]

theorem easCtorFinalMemory_version (registry owner : AccountAddress) :
    memLoad (UInt256.ofNat 256) (easCtorFinalMemory registry owner) = easCtorVersion := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,easCtorStringsMemory_size,ulit_toNat']; omega))) only
    [easCtorFinalMemory,easCtorRestoreMemory,easCtorDomainAllocated,easCtorDomainMemory,easCtorDomainPrefix,writeWordSequence,
      easCtorHashMemory,memLoad_write_below,memLoad_write_above,memLoad_write_at]

theorem easCtorFinalMemory_type (registry owner : AccountAddress) :
    memLoad (UInt256.ofNat 288) (easCtorFinalMemory registry owner) = easCtorType := by
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,easCtorStringsMemory_size,ulit_toNat']; omega))) only
    [easCtorFinalMemory,easCtorRestoreMemory,easCtorDomainAllocated,easCtorDomainMemory,easCtorDomainPrefix,writeWordSequence,
      easCtorHashMemory,memLoad_write_below,memLoad_write_above,memLoad_write_at]

end Benchmarks.EAS.EAS
