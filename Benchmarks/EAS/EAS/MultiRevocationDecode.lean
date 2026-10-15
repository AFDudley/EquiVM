import Benchmarks.EAS.EAS.RevocationArrayDecode
import Benchmarks.EAS.EAS.ReferencedArrayDecode
import Benchmarks.EAS.EAS.SchemaArrayDecode
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiRevocationABI : ABIType := .tuple [abiBytes32,.dynamicArray revocationDataABI]
def multiRevocationTuple (schema : UInt256) (rs : List RevocationRequestRecord) : Value :=
  .tuple [wordBytes32Value schema,.array (rs.map RevocationRequestRecord.tuple)]
def decodeMultiRevocationAt (cd : ByteArray) (root : UInt256) : Option (List RevocationRequestRecord) :=
  if requestArrayReferenceValid cd root then decodeRevocationArray cd (multiRequestArray cd root) else none
def decodeMultiRevocation (cd : ByteArray) (base : UInt256) (i : Nat) : Option (List RevocationRequestRecord) :=
  if multiRequestReferenceValid cd base i then decodeMultiRevocationAt cd (multiRequestRoot cd base i) else none
def multiRevocationValue (cd : ByteArray) (base : UInt256) (i : Nat) : Value :=
  ((decodeMultiRevocation cd base i).map (multiRevocationTuple (calldataWord cd (multiRequestRoot cd base i).toNat))).getD decodeFailure

theorem multiRevocationFields_decode (cd : ByteArray) (root : UInt256) (hsize : cd.size < 2^255+4) :
    (decodeFields? [abiBytes32,.dynamicArray revocationDataABI] cd.toList root.toNat 0
      [{materialize := []},{}] false).map Value.tuple =
      (decodeMultiRevocationAt cd root).map (multiRevocationTuple (calldataWord cd root.toNat)) := by
  rw [schemaArrayFields_decode revocationDataABI cd root
    (fun header => (decodeRevocationArray cd header).map (fun rs => .array (rs.map RevocationRequestRecord.tuple)))
    (fun header => revocationArray_decode cd header hsize)]
  by_cases hr : requestArrayReferenceValid cd root
  · simp only [decodeMultiRevocationAt,if_pos hr]
    cases decodeRevocationArray cd (multiRequestArray cd root) <;> rfl
  · simp only [decodeMultiRevocationAt,if_neg hr,Option.map_none]

theorem multiRevocation_decode (cd : ByteArray) (root : UInt256) (hsize : cd.size < 2^255+4) :
    decodeValue? multiRevocationABI cd.toList root.toNat multiRequestRowPlan true =
      (decodeMultiRevocationAt cd root).map (multiRevocationTuple (calldataWord cd root.toNat)) := by
  exact (schemaArray_decode revocationDataABI cd root).trans (multiRevocationFields_decode cd root hsize)

theorem multiRevocationElement_decode (cd : ByteArray) (base : UInt256) (i : Nat)
    (hb : base.toNat+32*i < UInt256.size) (hsize : cd.size < 2^255+4) :
    (do
      let target ← solcTailTarget? true multiRevocationABI cd.toList base.toNat (solcAdd base.toNat (32*i))
      decodeValue? multiRevocationABI cd.toList target multiRequestRowPlan true) =
      (decodeMultiRevocation cd base i).map (multiRevocationTuple (calldataWord cd (multiRequestRoot cd base i).toNat)) := by
  unfold multiRevocationABI
  rw [schemaArrayElement_decode revocationDataABI cd base i hb]
  by_cases hr : multiRequestReferenceValid cd base i
  · simp only [decodeMultiRevocation,if_pos hr]
    exact multiRevocation_decode cd _ hsize
  · simp only [decodeMultiRevocation,if_neg hr,Option.map_none]

def multiRevocationValues (cd : ByteArray) (base : UInt256) (n : Nat) : List Value :=
  (List.range n).map (multiRevocationValue cd base)

theorem multiRevocationElements_decode (cd : ByteArray) (base : UInt256) (i n : Nat)
    (hb : base.toNat+32*(i+n) < UInt256.size) (hsize : cd.size < 2^255+4) :
    decodeElements? multiRevocationABI n cd.toList base.toNat (32*i) multiRequestPlan true =
      some ((List.range' i n).map (multiRevocationValue cd base)) := by
  apply decodeReferencedElements (by native_decide) rfl rfl
  intro j hlo hhi
  rw [show child multiRequestPlan .element = multiRequestRowPlan by native_decide,
    multiRevocationElement_decode cd base j (by omega) hsize]
  simp only [retainFailure,show multiRequestRowPlan.deferErrors.contains [] = true from rfl,
    if_true,multiRevocationValue]

theorem multiRevocationArray_decode_eq (cd : ByteArray) (start : Nat) :
    decodeValue? (.dynamicArray multiRevocationABI) cd.toList start multiRequestPlan false =
      if solcMaxU64 < solcReadNat cd.toList start || badExtent true false cd.toList start (solcReadNat cd.toList start) 32 then none else
        (decodeElements? multiRevocationABI (solcReadNat cd.toList start) cd.toList
          (solcAdd start 32) 0 multiRequestPlan true).map Value.array := by
  exact referencedArray_decode_eq (by native_decide) rfl cd start

theorem decodeMultiRevocations_eq {cd : ByteArray} (name : Ident) (table : List (Nat × List CalldataPlan))
    (h4 : 4 ≤ cd.size) (hhead : solcSLT (solcSub cd.size 4) 32 = false)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = [multiRequestPlan]) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.dynamicArray multiRevocationABI] cd =
      if solcMaxU64 < solcReadNat cd.toList 4 then none else
        let start := solcAdd 4 (solcReadNat cd.toList 4)
        let size := solcReadNat cd.toList start
        if solcMaxU64 < size || badExtent true false cd.toList start size 32 then none else
          (decodeElements? multiRevocationABI size cd.toList (solcAdd start 32) 0 multiRequestPlan true).map
            (fun values => (∅ : Store).insert name (.array values)) := by
  exact decodeReferencedArray_eq (by native_decide) rfl rfl name table h4 hhead hplans

theorem decodeMultiRevocations {cd : ByteArray} (name : Ident) (table : List (Nat × List CalldataPlan))
    (h36 : 36 ≤ cd.size) (hbig : cd.size < 2^255+4) (hsize : cd.size < UInt256.size)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = [multiRequestPlan]) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.dynamicArray multiRevocationABI] cd =
      if wordArrayValid cd then some ((∅ : Store).insert name
        (.array (multiRevocationValues cd (UInt256.ofNat (wordArrayOffset cd+36)) (wordArrayLength cd)))) else none := by
  rw [decodeReferencedArray (ty := multiRevocationABI) (by native_decide) rfl rfl name table h36 hbig hsize hplans]
  by_cases hv : wordArrayValid cd
  · rw [if_pos hv,if_pos hv]
    have hb : (UInt256.ofNat (wordArrayOffset cd+36)).toNat = wordArrayOffset cd+36 := ulit_toNat' _ (by have := hv.2.2.2.2; omega)
    have he := multiRevocationElements_decode cd (UInt256.ofNat (wordArrayOffset cd+36)) 0 (wordArrayLength cd)
      (by rw [hb]; have := hv.2.2.2.2; omega) hbig
    simp only [hb,Nat.mul_zero,Nat.zero_add] at he
    rw [he]
    simp only [Option.map_some,multiRevocationValues,List.range_eq_range']
  · rw [if_neg hv,if_neg hv]

end Benchmarks.EAS.EAS
