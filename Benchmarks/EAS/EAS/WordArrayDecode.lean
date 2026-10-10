import Benchmarks.EAS.EAS.CalldataPlans
import Benchmarks.EAS.EAS.ArrayCalldataBounds
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
open ABI.Solc08Calldata
set_option maxRecDepth 10000

def wordArrayValue (cd : ByteArray) : Value :=
  .array ((calldataWordList cd (wordArrayOffset cd + 36) (wordArrayLength cd)).map wordBytes32Value)

-- LIBRARY CANDIDATE: a bounds characterization of the materialized bytes32-array decoder.
theorem decodeWordArray {cd : ByteArray} (name : Ident) (table : List (Nat × List CalldataPlan))
    (h36 : 36 ≤ cd.size) (hbig : cd.size < 2^255 + 4) (hsize : cd.size < UInt256.size)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = []) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.dynamicArray abiBytes32] cd =
      if wordArrayValid cd then some ((∅ : Store).insert name (wordArrayValue cd)) else none := by
  rw [decodeWordArray_eq name table (by omega)
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := false) (solcDecodeLenCheckOk_4_32 h36 hbig hsize)) hplans,
    solcReadNat_word h36 hsize]
  change (if solcMaxU64 < wordArrayOffset cd then none else
    let start := solcAdd 4 (wordArrayOffset cd)
    let size := solcReadNat cd.toList start
    if solcMaxU64 < size || badExtent true false cd.toList start size 32 then none else
      (decodeABIArrayStaticElems? abiBytes32 size 32
        (solcReadWords cd.toList (solcAdd start 32) size) 0).map
          (fun p => (∅ : Store).insert name (.array p.1))) = _
  rw [wordArrayGuards (fun start n => (decodeABIArrayStaticElems? abiBytes32 n 32
    (solcReadWords cd.toList start n) 0).map (fun p => (∅ : Store).insert name (.array p.1))) hsize]
  by_cases hv : wordArrayValid cd
  · rw [if_pos hv,if_pos hv,decodeSolcReadWords hv.2.2.2.2 hsize]
    simp only [Option.map_some,wordArrayValue]
  · rw [if_neg hv,if_neg hv]

theorem easPlans_empty_of_selector {I : ExecutionEnv} {idx : Nat}
    (hsel : selIs I (easSelBytes idx))
    (hplan : easPlans (bytesToWord (easSelBytes idx).toList).toNat = []) :
    easPlans (bytesToWord (I.calldata.toList.take 4)).toNat = [] :=
  easPlans_of_selector hsel hplan

theorem easDecodeWordArray {cd : ByteArray} (name : Ident)
    (h36 : 36 ≤ cd.size) (hbig : cd.size < 2^255 + 4) (hsize : cd.size < UInt256.size)
    (hplans : easPlans (bytesToWord (cd.toList.take 4)).toNat = []) :
    decodeCalldataWithMode config.abiDecodeMode [name] [.dynamicArray abiBytes32] cd =
      if wordArrayValid cd then some ((∅ : Store).insert name (wordArrayValue cd)) else none :=
  decodeWordArray name easPlanTable h36 hbig hsize hplans

end Benchmarks.EAS.EAS
