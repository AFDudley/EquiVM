import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! Apply deferred allocation-row decoding to the public reallocate selector. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

theorem reallocatePlans_of_selector {I : ExecutionEnv}
    (hsel : selIs I (metaMorphoV1_1SelBytes 34)) :
    ((reallocateCalldataPlans.find? (fun entry ↦ entry.1 ==
      (bytesToWord (I.calldata.toList.take 4)).toNat)).map Prod.snd).getD [] =
        [reallocateCalldataPlan] := by
  have hb : I.calldata.extract 0 4 = metaMorphoV1_1SelBytes 34 :=
    (byteArray_eq_of_beq hsel).symm
  have hl : I.calldata.toList.take 4 = (metaMorphoV1_1SelBytes 34).toList := by
    simpa only [byteArray_extract_toList, Nat.sub_zero, List.drop_zero] using
      congrArg ByteArray.toList hb
  rw [hl]
  decide +kernel

def reallocateArrayHead (cd : ByteArray) : UInt256 := ⟨4⟩ + calldataWord cd 4

def reallocateInput (cd : ByteArray) : List Value :=
  reallocateCalldataValues cd (reallocateArrayHead cd)

def reallocateCalldataLocals (cd : ByteArray) : Store :=
  (∅ : Store).insert "allocations" (.array (reallocateInput cd))

open Classical in
theorem reallocateDecodeRaw {I : ExecutionEnv}
    (hsel : selIs I (metaMorphoV1_1SelBytes 34)) :
    config.externalABI.decodeCalldata? (reallocateTransition.params.map (·.name))
        (reallocateTransition.params.map (·.ty)) I.calldata =
      if solcSLT (solcSub I.calldata.size 4) 32 then none
      else if solcMaxU64 < (calldataWord I.calldata 4).toNat then none
      else if solcMaxU64 < (calldataWord I.calldata (reallocateArrayHead I.calldata).toNat).toNat ||
          badExtent false false I.calldata.toList (reallocateArrayHead I.calldata).toNat
            (calldataWord I.calldata (reallocateArrayHead I.calldata).toNat).toNat 192 then none
      else some (reallocateCalldataLocals I.calldata) := by
  change decodeContractCalldata ["allocations"] [.dynamicArray reallocateItemType] I.calldata = _
  rw [decodeContractCalldata, if_neg (by decide), if_pos (by decide)]
  exact decodeReallocateCalldataRaw "allocations" reallocateCalldataPlans
    (calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 34) rfl hsel)
    (reallocatePlans_of_selector hsel)

end Benchmarks.Morpho.MetaMorphoV1_1
