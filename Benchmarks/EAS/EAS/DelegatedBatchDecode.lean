import Benchmarks.EAS.EAS.ReferencedArrayDecode
import Benchmarks.EAS.EAS.DelegatedAttestDecode
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

inductive DelegatedBatchSite where | attest | revoke

def DelegatedBatchSite.abi : DelegatedBatchSite → ABIType
  | .attest => .tuple [abiBytes32,.dynamicArray requestDataABI,.dynamicArray signatureABI,.elem .address]
  | .revoke => .tuple [abiBytes32,.dynamicArray revocationDataABI,.dynamicArray signatureABI,.elem .address]
def DelegatedBatchSite.plan : DelegatedBatchSite → CalldataPlan
  | .attest => {materialize := [[.element,.field 1,.element],[.element,.field 2,.element]],deferErrors := [[.element],[.element,.field 1],[.element,.field 2],[.element,.field 3],[.element,.field 1,.element],[.element,.field 2,.element]]}
  | .revoke => {materialize := [[.element]],deferErrors := [[.element]]}
def delegatedBatchElementDecode (site : DelegatedBatchSite) (cd : ByteArray) (base : UInt256) (i : Nat) : Option Value := do
  let target ← solcTailTarget? true site.abi cd.toList base.toNat (solcAdd base.toNat (32*i))
  decodeValue? site.abi cd.toList target (child site.plan .element) true
def delegatedBatchElement (site : DelegatedBatchSite) (cd : ByteArray) (base : UInt256) (i : Nat) : Value :=
  (delegatedBatchElementDecode site cd base i).getD decodeFailure
def delegatedBatchValues (site : DelegatedBatchSite) (cd : ByteArray) (base : UInt256) (n : Nat) : List Value :=
  (List.range n).map (delegatedBatchElement site cd base)

theorem delegatedBatchValues_length (site : DelegatedBatchSite) (cd : ByteArray) (base : UInt256) (n : Nat) :
    (delegatedBatchValues site cd base n).length = n := by simp only [delegatedBatchValues,List.length_map,List.length_range]
theorem delegatedBatchValues_get (site : DelegatedBatchSite) (cd : ByteArray) (base : UInt256) (n i : Nat) (hi : i<n) :
    (delegatedBatchValues site cd base n)[i]'(by rw [delegatedBatchValues_length]; exact hi) = delegatedBatchElement site cd base i := by
  simp only [delegatedBatchValues,List.getElem_map,List.getElem_range]

theorem delegatedBatchElements_decode (site : DelegatedBatchSite) (cd : ByteArray) (base : UInt256) (i n : Nat) :
    decodeElements? site.abi n cd.toList base.toNat (32*i) site.plan true =
      some ((List.range' i n).map (delegatedBatchElement site cd base)) := by
  apply decodeReferencedElements (by cases site <;> native_decide) (by cases site <;> rfl) (by cases site <;> rfl)
  intro j _ _
  simp only [retainFailure,show (child site.plan .element).deferErrors.contains [] = true by cases site <;> rfl,
    if_true,delegatedBatchElement,delegatedBatchElementDecode]

theorem decodeDelegatedBatch {cd : ByteArray} (site : DelegatedBatchSite) (name : Ident) (table : List (Nat × List CalldataPlan))
    (h36 : 36 ≤ cd.size) (hbig : cd.size < 2^255+4) (hsize : cd.size < UInt256.size)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = [site.plan]) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.dynamicArray site.abi] cd =
      if wordArrayValid cd then some ((∅ : Store).insert name (.array
        (delegatedBatchValues site cd (UInt256.ofNat (wordArrayOffset cd+36)) (wordArrayLength cd)))) else none := by
  rw [decodeReferencedArray (ty := site.abi) (by cases site <;> native_decide) (by cases site <;> rfl)
    (by cases site <;> rfl) name table h36 hbig hsize hplans]
  by_cases hv : wordArrayValid cd
  · rw [if_pos hv,if_pos hv]
    have hb : (UInt256.ofNat (wordArrayOffset cd+36)).toNat = wordArrayOffset cd+36 := ulit_toNat' _ (by have := hv.2.2.2.2; omega)
    have he := delegatedBatchElements_decode site cd (UInt256.ofNat (wordArrayOffset cd+36)) 0 (wordArrayLength cd)
    simp only [hb,Nat.mul_zero,Nat.zero_add] at he
    rw [he]
    simp only [Option.map_some,delegatedBatchValues,List.range_eq_range']
  · rw [if_neg hv,if_neg hv]

end Benchmarks.EAS.EAS
