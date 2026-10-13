import Benchmarks.EAS.EAS.DelegatedAttestationBatch
import Benchmarks.EAS.EAS.CopyRequestArrayStep
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestationRecords (cd : ByteArray) (root : UInt256) : List AttestationRequestRecord :=
  (List.range (delegatedAttestationDataLength cd root).toNat).map
    (fun i => requestDataRecord cd (requestArrayElement cd (delegatedAttestationDataOffset cd root) i))

theorem delegatedAttestationRecords_length (cd : ByteArray) (root : UInt256) :
    (delegatedAttestationRecords cd root).length=(delegatedAttestationDataLength cd root).toNat := by
  simp only [delegatedAttestationRecords,List.length_map,List.length_range]

theorem delegatedAttestationRecords_get (cd : ByteArray) (root : UInt256) (i : Nat)
    (hi : i<(delegatedAttestationRecords cd root).length) :
    (delegatedAttestationRecords cd root)[i]=requestDataRecord cd (requestArrayElement cd (delegatedAttestationDataOffset cd root) i) := by
  simp only [delegatedAttestationRecords,List.getElem_map,List.getElem_range]

theorem delegatedAttestationDataList_verified {cd : ByteArray} {root : UInt256}
    (hspan : (delegatedAttestationDataOffset cd root).toNat+32*(delegatedAttestationDataLength cd root).toNat<UInt256.size)
    (hgood : ∀ i, i<(delegatedAttestationDataLength cd root).toNat →
      delegatedAttestationDataValid cd (delegatedAttestationDataOffset cd root) i) :
    delegatedAttestationDataList cd root=(delegatedAttestationRecords cd root).map AttestationRequestRecord.tuple := by
  unfold delegatedAttestationDataList delegatedAttestationArrayValues retainedArrayValues delegatedAttestationRecords
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  change i<(delegatedAttestationDataLength cd root).toNat at hi
  have hslot : (delegatedAttestationDataOffset cd root).toNat+32*i<UInt256.size := by omega
  rw [delegatedAttestationData_element cd (delegatedBatchArray cd root 32+UInt256.ofNat 32) i hslot]
  change delegatedAttestationDatum cd (delegatedAttestationDataOffset cd root) i=_
  rw [delegatedAttestationDatum,if_pos (hgood i hi)]
  rfl

end Benchmarks.EAS.EAS
