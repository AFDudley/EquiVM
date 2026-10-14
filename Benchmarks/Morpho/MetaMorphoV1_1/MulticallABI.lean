import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayDecode
import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! Apply the calldata-reference decoder to multicall's declared entry point. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester (arrayHead)

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

theorem multicallPlans_of_selector {I : ExecutionEnv}
    (hsel : selIs I (metaMorphoV1_1SelBytes 50)) :
    ((multicallCalldataPlans.find? (fun entry ↦ entry.1 ==
      (bytesToWord (I.calldata.toList.take 4)).toNat)).map Prod.snd).getD [] =
        [multicallCalldataPlan] := by
  have hb : I.calldata.extract 0 4 = metaMorphoV1_1SelBytes 50 :=
    (byteArray_eq_of_beq hsel).symm
  have hl : I.calldata.toList.take 4 = (metaMorphoV1_1SelBytes 50).toList := by
    simpa only [byteArray_extract_toList, Nat.sub_zero, List.drop_zero] using
      congrArg ByteArray.toList hb
  rw [hl]
  decide +kernel

def multicallCalldataLocals (cd : ByteArray) : Store :=
  (∅ : Store).insert "data" (.array (calldataBytesArrayValues cd (arrayHead cd 4)))

open Classical in
theorem multicallDecode {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 50)) :
    config.externalABI.decodeCalldata? (multicallTransition.params.map (·.name))
      (multicallTransition.params.map (·.ty)) I.calldata =
        if WordArrayCalldataChecks I.calldata then some (multicallCalldataLocals I.calldata)
        else none := by
  change decodeContractCalldata ["data"] [.dynamicArray .bytes] I.calldata = _
  rw [decodeContractCalldata, if_pos (by decide)]
  exact decodeCalldataBytesArray "data" multicallCalldataPlans
    (calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 50) rfl hsel)
    hsize (multicallPlans_of_selector hsel)

end Benchmarks.Morpho.MetaMorphoV1_1
