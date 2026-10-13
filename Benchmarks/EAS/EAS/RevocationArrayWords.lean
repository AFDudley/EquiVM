import Benchmarks.EAS.EAS.StaticArrayDecode
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS

def revocationRecords (cd : ByteArray) (start n : Nat) : List RevocationRequestRecord :=
  (List.range n).map (fun i => revocationDataRecord cd (start+64*i))

theorem revocationRecords_length (cd : ByteArray) (start n : Nat) :
    (revocationRecords cd start n).length = n := by
  simp only [revocationRecords,List.length_map,List.length_range]

theorem revocationRecords_get (cd : ByteArray) (start n i : Nat) (hi : i < (revocationRecords cd start n).length) :
    (revocationRecords cd start n)[i] = revocationDataRecord cd (start+64*i) := by
  simp only [revocationRecords,List.getElem_map,List.getElem_range]

-- LIBRARY CANDIDATE: a complete word inside a bounded calldata slice.
theorem calldataSlice_word {cd : ByteArray} {start full off : Nat}
    (hb : start+full ≤ cd.size) (hi : off+32 ≤ full) :
    ((((cd.toList.drop start).take full).drop off).take 32) =
      EVM.Word.toBytesBE (calldataWord cd (start+off)) := by
  rw [List.drop_take,List.drop_drop,List.take_take,Nat.min_eq_left (by omega : 32 ≤ full-off)]
  have hlen : ((cd.toList.drop (start+off)).take 32).length = 32 := by
    rw [List.length_take,List.length_drop,byteArray_toList_eq,Array.length_toList]
    change min 32 (cd.size-(start+off)) = 32
    omega
  have hw : bytesToWord ((cd.toList.drop (start+off)).take 32) = calldataWord cd (start+off) :=
    decode_word_at_eq_any cd (start+off) (by omega)
  rw [← hw,toBytesBE_bytesToWord_of_length hlen]

theorem revocationArrayWords_decode {cd : ByteArray} {start n : Nat}
    (hb : start+64*n ≤ cd.size) (hsize : cd.size < UInt256.size) :
    decodeABIArrayStaticElems? revocationDataABI n 64 (solcReadWords cd.toList start (2*n)) 0 =
      some ((revocationRecords cd start n).map RevocationRequestRecord.tuple,64*n) := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  rw [solcReadWords_slice (by rw [hlen]; omega) (by rw [hlen]; exact hsize),show 32*(2*n) = 64*n by omega]
  let rs := revocationRecords cd start n
  have hdec := decodeStaticArray_of_elements (ty := revocationDataABI) (start := 0) (stride := 64)
    (bytes := (cd.toList.drop start).take (64*n)) (values := rs.map RevocationRequestRecord.tuple) (by
      intro i hi
      have hin : i < n := by simpa only [List.length_map,rs,revocationRecords_length] using hi
      have hu := calldataSlice_word (off := 64*i) hb (by omega)
      have hv := calldataSlice_word (off := 64*i+32) hb (by omega)
      have ht := decodeBytes32UIntTuple (start := 64*i)
        (by rw [hu,word_toBytesBE_length_32]) (by rw [hv,word_toBytesBE_length_32])
      rw [hu,hv,bytesToWord_toBytesBE] at ht
      simp only [List.getElem_map,revocationRecords_get,rs,Nat.zero_add]
      convert ht using 1 <;> simp only [revocationDataABI,revocationDataRecord,RevocationRequestRecord.tuple,
        wordBytes32Value,Nat.add_assoc,Nat.mul_add,Nat.mul_one])
  simpa only [List.length_map,rs,revocationRecords_length,Nat.zero_add] using hdec

end Benchmarks.EAS.EAS
