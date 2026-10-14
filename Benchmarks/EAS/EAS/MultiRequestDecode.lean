import Benchmarks.EAS.EAS.RequestArrayDecode
import Benchmarks.EAS.EAS.SchemaArrayDecode
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiRequestABI : ABIType := .tuple [abiBytes32,.dynamicArray requestDataABI]
def multiRequestTuple (schema : UInt256) (rs : List AttestationRequestRecord) : Value :=
  .tuple [wordBytes32Value schema,.array (rs.map AttestationRequestRecord.tuple)]
def decodeMultiRequestAt (cd : ByteArray) (root : UInt256) : Option (List AttestationRequestRecord) :=
  if requestArrayReferenceValid cd root then decodeRequestArray cd (multiRequestArray cd root) else none
def decodeMultiRequest (cd : ByteArray) (base : UInt256) (i : Nat) : Option (List AttestationRequestRecord) :=
  if multiRequestReferenceValid cd base i then decodeMultiRequestAt cd (multiRequestRoot cd base i) else none
def multiRequestValue (cd : ByteArray) (base : UInt256) (i : Nat) : Value :=
  ((decodeMultiRequest cd base i).map (multiRequestTuple (calldataWord cd (multiRequestRoot cd base i).toNat))).getD decodeFailure

theorem multiRequestFields_decode (cd : ByteArray) (root : UInt256) (hsize : cd.size < 2^255+4) :
    (decodeFields? [abiBytes32,.dynamicArray requestDataABI] cd.toList root.toNat 0
      [{materialize := []},{}] false).map Value.tuple =
      (decodeMultiRequestAt cd root).map (multiRequestTuple (calldataWord cd root.toNat)) := by
  rw [schemaArrayFields_decode requestDataABI cd root
    (fun header => (decodeRequestArray cd header).map (fun rs => .array (rs.map AttestationRequestRecord.tuple)))
    (fun header => requestArray_decode cd header hsize)]
  by_cases hr : requestArrayReferenceValid cd root
  · simp only [decodeMultiRequestAt,if_pos hr]
    cases decodeRequestArray cd (multiRequestArray cd root) <;> rfl
  · simp only [decodeMultiRequestAt,if_neg hr,Option.map_none]

theorem multiRequest_decode (cd : ByteArray) (root : UInt256) (hsize : cd.size < 2^255+4) :
    decodeValue? multiRequestABI cd.toList root.toNat multiRequestRowPlan true =
      (decodeMultiRequestAt cd root).map (multiRequestTuple (calldataWord cd root.toNat)) := by
  exact (schemaArray_decode requestDataABI cd root).trans (multiRequestFields_decode cd root hsize)

theorem multiRequestElement_decode (cd : ByteArray) (base : UInt256) (i : Nat)
    (hb : base.toNat+32*i < UInt256.size) (hsize : cd.size < 2^255+4) :
    (do
      let target ← solcTailTarget? true multiRequestABI cd.toList base.toNat (solcAdd base.toNat (32*i))
      decodeValue? multiRequestABI cd.toList target multiRequestRowPlan true) =
      (decodeMultiRequest cd base i).map (multiRequestTuple (calldataWord cd (multiRequestRoot cd base i).toNat)) := by
  unfold multiRequestABI
  rw [schemaArrayElement_decode requestDataABI cd base i hb]
  by_cases hr : multiRequestReferenceValid cd base i
  · simp only [decodeMultiRequest,if_pos hr]
    exact multiRequest_decode cd _ hsize
  · simp only [decodeMultiRequest,if_neg hr,Option.map_none]

end Benchmarks.EAS.EAS
