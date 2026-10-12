import Benchmarks.EAS.EAS.ConstructorMemoryBase
import Benchmarks.EAS.EAS.ConstructorSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: an in-bounds word write in the suffix leaves its prefix intact.
theorem writeWord_append_prefix (pre post : ByteArray) (off : Nat) (word : UInt256) (hb : off+32 ≤ post.size) :
    writeWord (pre++post) (pre.size+off) word = pre++writeWord post off word := by
  have hp : (pre++post).extract 0 (pre.size+off) = pre++post.extract 0 off := by
    rw [ByteArray.extract_append]
    have hs : pre.extract 0 (pre.size+off) = pre := by
      apply ByteArray.ext
      rw [ByteArray.data_extract,Array.extract_eq_self_of_le (by change pre.size ≤ pre.size+off; omega)]
    rw [hs]
    simp only [Nat.zero_sub,Nat.add_sub_cancel_left]
  have ht : (pre++post).extract (pre.size+off+32) (pre.size+post.size) = post.extract (off+32) post.size := by
    rw [extract_append_right_window _ _ _ _ (by omega)]
    congr 1 <;> omega
  rw [Reasoning.Theory.writeWord,write_eq_gen _ _ _ _ (by decide) (by rw [toByteArray_size]) (by rw [ByteArray.size_append]; omega),
    hp,ByteArray.size_append,ht,Reasoning.Theory.writeWord,write_eq_gen _ _ _ _ (by decide) (by rw [toByteArray_size]) hb]
  simp only [ByteArray.append_assoc]

def easCtorPatches (registry owner : AccountAddress) : List (Nat × UInt256) :=
  [(14029,easCtorDomain owner),(14218,UInt256.ofNat Ethereum.chainId),(13982,UInt256.ofNat owner.val),
    (14108,easCtorName),(14146,easCtorVersion),(14073,easCtorType),
    (678,UInt256.ofNat registry.val),(7761,UInt256.ofNat registry.val),(9982,UInt256.ofNat registry.val),
    (12162,UInt256.ofNat registry.val),(12821,UInt256.ofNat registry.val)]
def easCtorRuntime (registry owner : AccountAddress) : ByteArray := writeCascade easBytecode (easCtorPatches registry owner)

theorem easCtorPatchedRuntime_size (registry owner : AccountAddress) : (easCtorRuntime registry owner).size = 17208 := by
  simp only [easCtorRuntime,easCtorPatches,writeCascade,writeWord_sparse_size,easBytecode_size]; rfl

theorem easCtorRuntime_deployed (registry owner : AccountAddress) :
    easCtorRuntime registry owner = immutableLayout.deployed easBytecode (easCtorImms owner registry) := by
  have hword (w : UInt256) : valueToWord (.int (Int.ofNat w.toNat)) = some w := by
    simp only [valueToWord,pure,wordOfInt_ofNat_toNat_gen,u256_ofNat_toNat]
  have haddr (a : AccountAddress) : valueToWord (.address a) = some (UInt256.ofNat a.val) := rfl
  simp only [easCtorRuntime,easCtorPatches,Layout.deployed,Layout.runtime,Layout.writes,immutableLayout,
    immutableReferences,List.flatMap_cons,List.flatMap_nil,List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.append_nil,
    wordsOf_of_get (easCtorImms_get_CACHED_DOMAIN_SEPARATOR owner registry) (hword _),
    wordsOf_of_get (easCtorImms_get_CACHED_CHAIN_ID owner registry) (hword _),
    wordsOf_of_get (easCtorImms_get_CACHED_THIS owner registry) (haddr _),
    wordsOf_of_get (easCtorImms_get_HASHED_NAME owner registry) (hword _),
    wordsOf_of_get (easCtorImms_get_HASHED_VERSION owner registry) (hword _),
    wordsOf_of_get (easCtorImms_get_TYPE_HASH owner registry) (hword _),
    wordsOf_of_get (easCtorImms_get_schemaRegistry owner registry) (haddr _)]

theorem easCtorRuntime_read (pre : ByteArray) (registry owner : AccountAddress) (hs : pre.size = 704) :
    (pre++easCtorRuntime registry owner).readWithPadding 704 17208 = immutableLayout.deployed easBytecode (easCtorImms owner registry) := by
  rw [readWithPadding_eq_extract' _ _ _ (by decide) (by decide) (by rw [ByteArray.size_append,hs,easCtorPatchedRuntime_size]),
    extract_append_right' _ _ _ _ hs.symm (by rw [hs,easCtorPatchedRuntime_size]),easCtorRuntime_deployed]

end Benchmarks.EAS.EAS
