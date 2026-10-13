import Benchmarks.EAS.EAS.ResolverManyData
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: concatenating uniformly bounded byte strings bounds the total size.
theorem dynamicBodies_size_bound (bs : List ByteArray) (limit : Nat) (h : ∀ b ∈ bs, b.size ≤ limit) :
    (dynamicBodies bs).size ≤ bs.length*limit := by
  induction bs with
  | nil => simp only [dynamicBodies, ByteArray.size_empty, List.length_nil, Nat.zero_mul, le_refl]
  | cons b bs ih =>
    have hb := h b (by simp)
    have hr := ih (fun x hx => h x (by simp only [List.mem_cons]; exact Or.inr hx))
    simp only [dynamicBodies, ByteArray.size_append, List.length_cons]
    rw [Nat.add_mul]
    omega

theorem AttestationArrayMemoryView.data_bound {mem : ByteArray} {ptr : UInt256} {ats : List AttestationRecord} {limit : Nat}
    (h : AttestationArrayMemoryView mem ptr ats limit) : ∀ a ∈ ats, a.data.size ≤ limit := by
  refine (List.forall_mem_iff_getElem (l := ats) (p := fun a => a.data.size ≤ limit)).mpr ?_
  intro i hi
  obtain ⟨src,dp,hs,hv,hsrc,hdata⟩ := h.records i hi
  omega

theorem AttestationArrayMemoryView.encoding_bound {mem : ByteArray} {ptr : UInt256} {ats : List AttestationRecord} {limit : Nat}
    (h : AttestationArrayMemoryView mem ptr ats limit) : ∀ a ∈ ats, a.encoding.size ≤ limit+352 := by
  refine (List.forall_mem_iff_getElem (l := ats) (p := fun a => a.encoding.size ≤ limit+352)).mpr ?_
  intro i hi
  obtain ⟨src,dp,hs,hv,hsrc,hdata⟩ := h.records i hi
  rw [AttestationRecord.encoding_size]
  omega

theorem resolverManyBody_bound {mem : ByteArray} {array valuesPtr : UInt256} {ats : List AttestationRecord}
    {values : List UInt256} {limit : Nat}
    (harray : AttestationArrayMemoryView mem array ats limit)
    (hvalues : WordArrayMemoryView mem valuesPtr values limit)
    (hlimit : limit ≤ 2^64-1) : 4+(resolverArraysBody ats values).size < 2^130 := by
  have hlen : ats.length ≤ 2^64 := by have := harray.span; omega
  have hvlen : values.length ≤ 2^64 := by have := hvalues.span; omega
  have hb : (attestationArrayBodies ats ats.length).size ≤ ats.length*(2^64+352) := by
    have he : ∀ b ∈ ats.map AttestationRecord.encoding, b.size ≤ 2^64+352 := by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      have he := harray.encoding_bound a ha
      omega
    simpa only [attestationArrayBodies, List.take_length, List.length_map] using
      dynamicBodies_size_bound (ats.map AttestationRecord.encoding) (2^64+352) he
  have hb' : (attestationArrayBodies ats ats.length).size ≤ (2^64)*(2^64+352) :=
    le_trans hb (Nat.mul_le_mul_right _ hlen)
  rw [resolverArraysBody_size, attestationArrayEncoding_size, attestationArrayOffset]
  omega

theorem resolverManyPayload_small {mem : ByteArray} {array valuesPtr : UInt256} {ats : List AttestationRecord}
    {values : List UInt256} {limit : Nat} (rev : Bool)
    (harray : AttestationArrayMemoryView mem array ats limit)
    (hvalues : WordArrayMemoryView mem valuesPtr values limit)
    (hlimit : limit ≤ 2^64-1) : (resolverManyPayload ats values rev).size ≤ Ethereum.EVM.maxReturnDataSizeByGas := by
  have hmax : 2^130 ≤ Ethereum.EVM.maxReturnDataSizeByGas := by decide +kernel
  rw [resolverManyPayload_size]
  exact le_trans (Nat.le_of_lt (resolverManyBody_bound harray hvalues hlimit)) hmax

end Benchmarks.EAS.EAS
