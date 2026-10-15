import Benchmarks.EAS.EAS.ScalarDecode
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES easPlans_empty_of_selector to any concrete decoder plan.
theorem easPlans_of_selector {I : ExecutionEnv} {idx : Nat} {plans : List CalldataPlan}
    (hsel : selIs I (easSelBytes idx))
    (hplan : easPlans (bytesToWord (easSelBytes idx).toList).toNat = plans) :
    easPlans (bytesToWord (I.calldata.toList.take 4)).toNat = plans := by
  have hbytes : I.calldata.extract 0 4 = easSelBytes idx := (byteArray_eq_of_beq hsel).symm
  have hl : I.calldata.toList.take 4 = (easSelBytes idx).toList := by
    simpa only [byteArray_extract_toList,Nat.sub_zero,List.drop_zero] using congrArg ByteArray.toList hbytes
  rw [hl]
  exact hplan


end Benchmarks.EAS.EAS
