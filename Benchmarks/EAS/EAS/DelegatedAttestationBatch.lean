import Benchmarks.EAS.EAS.DelegatedAttestationFacts
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestationDataList (cd : ByteArray) (root : UInt256) : List Value :=
  delegatedAttestationArrayValues requestDataABI cd (delegatedBatchArray cd root 32) 32
def delegatedAttestationSigList (cd : ByteArray) (root : UInt256) : List Value :=
  delegatedAttestationArrayValues signatureABI cd (delegatedBatchArray cd root 64) 96
def delegatedAttestationDataOffset (cd : ByteArray) (root : UInt256) : UInt256 := delegatedBatchArray cd root 32+UInt256.ofNat 32
def delegatedAttestationSigOffset (cd : ByteArray) (root : UInt256) : UInt256 := delegatedBatchArray cd root 64+UInt256.ofNat 32
def delegatedAttestationDataLength (cd : ByteArray) (root : UInt256) : UInt256 := calldataWord cd (delegatedBatchArray cd root 32).toNat
def delegatedAttestationSigLength (cd : ByteArray) (root : UInt256) : UInt256 := calldataWord cd (delegatedBatchArray cd root 64).toNat

structure DelegatedAttestationBatchReady (cd : ByteArray) (root : UInt256) : Prop where
  data : requestArrayAccessValid cd root
  signatures : signatureArrayReferenceAccessValid cd root
  nonempty : 0<(delegatedAttestationDataLength cd root).toNat
  lengths : delegatedAttestationDataLength cd root=delegatedAttestationSigLength cd root

theorem delegatedAttestationDataList_length (cd : ByteArray) (root : UInt256) :
    (delegatedAttestationDataList cd root).length=(delegatedAttestationDataLength cd root).toNat := delegatedAttestationArrayValues_length ..
theorem delegatedAttestationSigList_length (cd : ByteArray) (root : UInt256) :
    (delegatedAttestationSigList cd root).length=(delegatedAttestationSigLength cd root).toNat := delegatedAttestationArrayValues_length ..

theorem DelegatedAttestationBatchReady.bounds {cd : ByteArray} {root : UInt256}
    (h : DelegatedAttestationBatchReady cd root) (hsize : cd.size<2^255) :
    (delegatedAttestationDataLength cd root).toNat≤2^64-1 ∧
    (delegatedAttestationDataOffset cd root).toNat+32*(delegatedAttestationDataLength cd root).toNat<UInt256.size ∧
    (delegatedAttestationSigOffset cd root).toNat+96*(delegatedAttestationDataLength cd root).toNat<UInt256.size := by
  have hd := ((delegatedAttestationRequestAccess cd root).mp h.data).2
  have hs := ((delegatedAttestationSignatureAccess cd root).mp h.signatures).2
  refine ⟨hd.1,referencedArrayNonempty_span hsize (by decide) hd h.nonempty,?_⟩
  rw [h.lengths]
  exact referencedArrayNonempty_span hsize (by decide) hs (by change 0<(delegatedAttestationSigLength cd root).toNat;rw [← h.lengths];exact h.nonempty)

theorem DelegatedAttestationBatchReady.tuple {cd : ByteArray} {root : UInt256}
    (h : DelegatedAttestationBatchReady cd root) :
    delegatedAttestationTuple cd root=Value.tuple [wordBytes32Value (calldataWord cd root.toNat),
      .array (delegatedAttestationDataList cd root),.array (delegatedAttestationSigList cd root),delegatedAttestationAddressValue cd root] := by
  simp only [delegatedAttestationTuple,delegatedAttestationArrayValue,
    if_pos ((delegatedAttestationRequestAccess cd root).mp h.data),
    if_pos ((delegatedAttestationSignatureAccess cd root).mp h.signatures)]
  rfl

theorem delegatedAttestationSigIndex_word {cd : ByteArray} {root : UInt256} {j : Nat}
    (hj : j<UInt256.size) (hb : (delegatedAttestationSigOffset cd root).toNat+96*j<UInt256.size) :
    UInt256.mul (UInt256.ofNat j) (UInt256.ofNat 96)+delegatedAttestationSigOffset cd root=
      UInt256.ofNat ((delegatedAttestationSigOffset cd root).toNat+96*j) := by
  rw [wordMul_nat _ 96 (by decide),ulit_toNat' _ hj,u256_add_comm]
  apply u256_inj
  rw [uadd_word_ofNat_toNat _ _ hb,ulit_toNat' _ hb]

end Benchmarks.EAS.EAS
