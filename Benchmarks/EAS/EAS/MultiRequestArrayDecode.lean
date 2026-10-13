import Benchmarks.EAS.EAS.MultiRequestElements
import Benchmarks.EAS.EAS.ArrayCalldataBounds
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem multiRequestArray_decode_eq (cd : ByteArray) (start : Nat) :
    decodeValue? (.dynamicArray multiRequestABI) cd.toList start multiRequestPlan false =
      if solcMaxU64 < solcReadNat cd.toList start || badExtent true false cd.toList start (solcReadNat cd.toList start) 32 then none else
        (decodeElements? multiRequestABI (solcReadNat cd.toList start) cd.toList
          (solcAdd start 32) 0 multiRequestPlan true).map Value.array := by
  exact referencedArray_decode_eq (by native_decide) rfl cd start

theorem decodeMultiRequests_eq {cd : ByteArray} (name : Ident) (table : List (Nat × List CalldataPlan))
    (h4 : 4 ≤ cd.size) (hhead : solcSLT (solcSub cd.size 4) 32 = false)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = [multiRequestPlan]) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.dynamicArray multiRequestABI] cd =
      if solcMaxU64 < solcReadNat cd.toList 4 then none else
        let start := solcAdd 4 (solcReadNat cd.toList 4)
        let size := solcReadNat cd.toList start
        if solcMaxU64 < size || badExtent true false cd.toList start size 32 then none else
          (decodeElements? multiRequestABI size cd.toList (solcAdd start 32) 0 multiRequestPlan true).map
            (fun values => (∅ : Store).insert name (.array values)) := by
  exact decodeReferencedArray_eq (by native_decide) rfl rfl name table h4 hhead hplans

theorem decodeMultiRequests {cd : ByteArray} (name : Ident) (table : List (Nat × List CalldataPlan))
    (h36 : 36 ≤ cd.size) (hbig : cd.size < 2^255+4) (hsize : cd.size < UInt256.size)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = [multiRequestPlan]) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.dynamicArray multiRequestABI] cd =
      if wordArrayValid cd then some ((∅ : Store).insert name
        (.array (multiRequestValues cd (UInt256.ofNat (wordArrayOffset cd+36)) (wordArrayLength cd)))) else none := by
  rw [decodeReferencedArray (ty := multiRequestABI) (by native_decide) rfl rfl name table h36 hbig hsize hplans]
  by_cases hv : wordArrayValid cd
  · rw [if_pos hv,if_pos hv]
    have hb : (UInt256.ofNat (wordArrayOffset cd+36)).toNat = wordArrayOffset cd+36 := ulit_toNat' _ (by have := hv.2.2.2.2; omega)
    have he := multiRequestElements_decode cd (UInt256.ofNat (wordArrayOffset cd+36)) 0 (wordArrayLength cd)
      (by rw [hb]; have := hv.2.2.2.2; omega) hbig
    simp only [hb,Nat.mul_zero,Nat.zero_add] at he
    rw [he]
    simp only [Option.map_some,multiRequestValues,List.range_eq_range']
  · rw [if_neg hv,if_neg hv]

end Benchmarks.EAS.EAS
