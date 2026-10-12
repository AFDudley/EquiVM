import Benchmarks.EAS.EAS.ConstructorDomainMemory
import Benchmarks.EAS.EAS.ConstructorPatch
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: appending bytes preserves initialized loads from the prefix.
theorem memLoad_append_prefix (pre post : ByteArray) (ptr : UInt256) (hin : ptr.toNat+32 ≤ pre.size) :
    memLoad ptr (pre++post) = memLoad ptr pre := by
  simp only [memLoad]
  rw [if_neg (by rw [ByteArray.size_append]; omega),if_neg (by omega),
    readWithPadding_eq_extract _ _ (by rw [ByteArray.size_append]; omega),
    extract_append_left _ _ _ _ hin,readWithPadding_eq_extract _ _ hin]

def easCtorReturnPrefix (registry owner : AccountAddress) : ByteArray :=
  writeWord (easCtorFinalMemory registry owner) 320 (UInt256.ofNat registry.val)
def easCtorReturnMemory9 (registry owner : AccountAddress) : ByteArray := writeCascade
  (easCtorReturnPrefix registry owner++easBytecode)
  ((easCtorPatches registry owner).take 9 |>.map fun (o,w) => (704+o,w))
def easCtorReturnMemory (registry owner : AccountAddress) : ByteArray :=
  writeWord (writeWord (easCtorReturnMemory9 registry owner) (704+12162) (UInt256.ofNat registry.val)) (704+12821) (UInt256.ofNat registry.val)

theorem easCtorReturnPrefix_size (registry owner : AccountAddress) : (easCtorReturnPrefix registry owner).size = 704 := by
  rw [easCtorReturnPrefix,writeWord_sparse_size,easCtorFinalMemory_size]; rfl
theorem easCtorReturnPrefix_load (registry owner : AccountAddress) (ptr : UInt256) (hlo : ptr.toNat+32 ≤ 320) :
    memLoad ptr (easCtorReturnPrefix registry owner) = memLoad ptr (easCtorFinalMemory registry owner) := by
  rw [easCtorReturnPrefix,memLoad_write_below _ _ _ _ hlo (by rw [easCtorFinalMemory_size]; omega)]
theorem easCtorReturnPrefix_registry (registry owner : AccountAddress) : memLoad (UInt256.ofNat 320) (easCtorReturnPrefix registry owner) = UInt256.ofNat registry.val :=
  memLoad_write_at _ _ _ (by decide)
theorem easCtorReturnPrefix_free (registry owner : AccountAddress) : memLoad (UInt256.ofNat 64) (easCtorReturnPrefix registry owner) = UInt256.ofNat 704 := by
  rw [easCtorReturnPrefix_load _ _ _ (by decide),easCtorFinalMemory_free]

theorem easCtorCopyRuntime (registry owner : AccountAddress) :
    (easCtorCode registry).write 434 (easCtorReturnPrefix registry owner) 704 17208 = easCtorReturnPrefix registry owner++easBytecode := by
  rw [← easCtorReturnPrefix_size registry owner,write_at_end_eq_from _ _ _ _ (by decide) (by rw [easCtorCode_size]; decide),easCtorCode_runtime]

theorem easCtorReturnMemory_eq (registry owner : AccountAddress) :
    easCtorReturnMemory registry owner = easCtorReturnPrefix registry owner++easCtorRuntime registry owner := by
  have hw (post : ByteArray) (off : Nat) (w : UInt256) (hb : off+32 ≤ post.size) :
      writeWord (easCtorReturnPrefix registry owner++post) (704+off) w = easCtorReturnPrefix registry owner++writeWord post off w := by
    simpa only [easCtorReturnPrefix_size] using writeWord_append_prefix (easCtorReturnPrefix registry owner) post off w hb
  simp (disch := (simp only [writeWord_sparse_size,easBytecode_size]; decide)) only
    [easCtorReturnMemory,easCtorReturnMemory9,easCtorRuntime,easCtorPatches,List.take_succ_cons,List.take_zero,
      List.map_cons,List.map_nil,writeCascade,hw]

theorem easCtorReturnMemory_read (registry owner : AccountAddress) :
    (easCtorReturnMemory registry owner).readWithPadding 704 17208 = immutableLayout.deployed easBytecode (easCtorImms owner registry) := by
  rw [easCtorReturnMemory_eq]
  exact easCtorRuntime_read _ _ _ (easCtorReturnPrefix_size _ _)

end Benchmarks.EAS.EAS
