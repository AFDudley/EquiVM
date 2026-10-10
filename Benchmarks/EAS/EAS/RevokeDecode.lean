import Benchmarks.EAS.EAS.RevocationRequest
import Benchmarks.EAS.EAS.CalldataPlans
import Benchmarks.EAS.EAS.WordArrayBase
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def revocationDataABI : ABIType := .tuple [abiBytes32,abiUInt256]
def revokeRequestABI : ABIType := .tuple [abiBytes32,revocationDataABI]
def revocationDataRecord (cd : ByteArray) (start : Nat) : RevocationRequestRecord :=
  ⟨calldataWord cd start,calldataWord cd (start+32)⟩
def revokeRequestValue (cd : ByteArray) : Value :=
  .tuple [wordBytes32Value (calldataWord cd 4),(revocationDataRecord cd 36).tuple]

-- LIBRARY CANDIDATE: a static bytes32/uint256 tuple at any byte offset.
theorem decodeBytes32UIntTuple {bytes : List UInt8} {start : Nat}
    (ha : ((bytes.drop start).take 32).length = 32)
    (hb : ((bytes.drop (start+32)).take 32).length = 32) :
    decodeABIValue? (.tuple [abiBytes32,abiUInt256]) bytes start =
      some (.tuple [.fixedBytes abiBytes32Width ((bytes.drop start).take 32),
        .int (Int.ofNat (bytesToWord ((bytes.drop (start+32)).take 32)).toNat)],start+64) := by
  rw [decodeABIValue?]
  simp only [bind,show abiTupleHeadSize? [abiBytes32,abiUInt256] = some 64 by native_decide,bind,Option.bind]
  simp only [bind,decodeABIValues?,show isDynamicABIType abiBytes32 = false from rfl,
    show isDynamicABIType abiUInt256 = false from rfl,show staticABIEncodedSize? abiBytes32 = some 32 from rfl,
    show staticABIEncodedSize? abiUInt256 = some 32 from rfl,Bool.false_eq_true,if_false,Option.bind,
    Nat.add_zero,Nat.zero_add]
  rw [decodeABIValue_bytes32_ok ha]
  simp only [bind,Option.bind,if_true]
  rw [decodeABIValue_uint256_ok hb]
  simp only [bind,Option.bind,if_true,pure,show start+32+32 = start+64 by omega,
    Nat.max_eq_left (by omega : start+32 ≤ start+64),Nat.max_self]

theorem decodeRevokeTuple {bytes : List UInt8} {start : Nat}
    (ha : ((bytes.drop start).take 32).length = 32)
    (hb : ((bytes.drop (start+32)).take 32).length = 32)
    (hc : ((bytes.drop (start+64)).take 32).length = 32) :
    decodeABIValue? revokeRequestABI bytes start =
      some (.tuple [.fixedBytes abiBytes32Width ((bytes.drop start).take 32),
        .tuple [.fixedBytes abiBytes32Width ((bytes.drop (start+32)).take 32),
          .int (Int.ofNat (bytesToWord ((bytes.drop (start+64)).take 32)).toNat)]],start+96) := by
  rw [revokeRequestABI,decodeABIValue?]
  simp only [bind,show abiTupleHeadSize? [abiBytes32,revocationDataABI] = some 96 by native_decide,bind,Option.bind]
  simp only [bind,decodeABIValues?,show isDynamicABIType abiBytes32 = false from rfl,
    show isDynamicABIType revocationDataABI = false from rfl,show staticABIEncodedSize? abiBytes32 = some 32 from rfl,
    show staticABIEncodedSize? revocationDataABI = some 64 from rfl,Bool.false_eq_true,if_false,Option.bind,
    Nat.add_zero,Nat.zero_add]
  rw [decodeABIValue_bytes32_ok ha]
  simp only [bind,Option.bind,if_true]
  rw [show revocationDataABI = .tuple [abiBytes32,abiUInt256] from rfl,
    decodeBytes32UIntTuple hb (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hc)]
  simp only [bind,Option.bind,if_true,pure,Nat.add_assoc,Nat.reduceAdd,
    Nat.max_eq_left (by omega : start+32 ≤ start+96),Nat.max_self]

theorem decodeRevoke {cd : ByteArray} (name : Ident) (table : List (Nat × List CalldataPlan))
    (hsize : cd.size < UInt256.size) (h100 : 100 ≤ cd.size)
    (hhead : solcSLT (solcSub cd.size 4) 96 = false)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = []) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [revokeRequestABI] cd =
      some ((∅ : Store).insert name (revokeRequestValue cd)) := by
  rw [decodeCalldataSolc08,if_neg (by omega : ¬ cd.size < 4)]
  simp only [bind,decodeArgs?,List.isEmpty_cons,Bool.false_eq_true,if_false,
    show abiTupleHeadSize? [revokeRequestABI] = some 96 by native_decide,bind,Option.bind,hhead,hplans]
  simp only [bind,decodeFields?,show stride? revokeRequestABI = some 96 from rfl,
    show isDynamicABIType revokeRequestABI = false from rfl,List.headD_nil,List.tail_nil,retainFailure,
    show ({} : CalldataPlan).deferErrors.contains [] = false from rfl,
    Bool.false_eq_true,if_false,Bool.false_and,show solcAdd 4 0 = 4 from rfl,Option.bind,pure]
  rw [revokeRequestABI,decodeValue?]
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  simp only [bind,show abiTupleHeadSize? [abiBytes32,revocationDataABI] = some 96 by native_decide,
    show isDynamicABIType (.tuple [abiBytes32,revocationDataABI]) = false from rfl,
    Bool.not_false,Bool.true_or,Bool.true_and,Option.bind,hlen,hhead,if_false,if_true]
  have hw := solcReadWords_flatMap (start := 4) (count := 3) (by omega : 4+32*3 ≤ cd.size) hsize
  rw [show 96/32 = 3 from rfl,hw]
  let ws := (calldataWordList cd 4 3).flatMap EVM.Word.toBytesBE
  have wl : ws.length = 96 := by
    simp only [bind,ws,calldataWordList,List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,word_toBytesBE_length_32,List.length_nil,Nat.reduceAdd]
  have ht (off : Nat) (ho : off ≤ 64) : ((ws.drop off).take 32).length = 32 := by
    rw [List.length_take,List.length_drop,wl]; omega
  have hdecoded := decodeRevokeTuple (ht 0 (by decide)) (ht 32 (by decide)) (ht 64 (by decide))
  simp only [revokeRequestABI] at hdecoded
  rw [hdecoded]
  simp only [bind,Option.map_some,Option.bind,decodeCalldata.insertValues,Bool.false_eq_true,if_false]
  congr 2
  have hwords : ws = EVM.Word.toBytesBE (calldataWord cd 4) ++ EVM.Word.toBytesBE (calldataWord cd 36) ++
      EVM.Word.toBytesBE (calldataWord cd 68) := by
    simp only [ws,calldataWordList,List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.nil_append,Nat.reduceAdd,Nat.reduceMul]
  have htake (w : UInt256) : (EVM.Word.toBytesBE w).take 32 = EVM.Word.toBytesBE w :=
    List.take_of_length_le (by rw [word_toBytesBE_length_32])
  have hdrop32 (w : UInt256) : (EVM.Word.toBytesBE w).drop 32 = [] :=
    List.drop_of_length_le (by rw [word_toBytesBE_length_32])
  have hdrop64 (w : UInt256) : (EVM.Word.toBytesBE w).drop 64 = [] :=
    List.drop_of_length_le (by rw [word_toBytesBE_length_32]; decide)
  simp only [hwords,List.drop_zero,List.take_append,List.drop_append,List.length_append,word_toBytesBE_length_32,
    htake,hdrop32,hdrop64,Nat.reduceAdd,Nat.reduceSub,List.take_zero,List.nil_append,List.append_nil,
    bytesToWord_toBytesBE,revokeRequestValue,revocationDataRecord,RevocationRequestRecord.tuple,wordBytes32Value]

end Benchmarks.EAS.EAS
