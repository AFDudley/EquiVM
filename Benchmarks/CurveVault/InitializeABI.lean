import Benchmarks.CurveVault.InitializeLocals
import Benchmarks.CurveVault.ScalarCalldata

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultInitializeDecode (cd : ByteArray) (hsize : 132 ≤ cd.size) :
    config.externalABI.decodeCalldata? (initializeTransition.params.map Param.name)
      (transitionSignature initializeTransition).paramTypes cd =
      if (calldataWord cd 4).toNat < EVM.addressModulus then
        if (calldataWord cd 36).toNat < EVM.addressModulus then
          if (calldataWord cd 68).toNat < EVM.addressModulus then
            if (calldataWord cd 100).toNat < EVM.addressModulus then
              some (vaultInitializeLocals (calldataWord cd 4) (calldataWord cd 36)
                (calldataWord cd 68) (calldataWord cd 100))
            else none
          else none
        else none
      else none := by
  change decodeCalldataWithMode .vyper ["_amm_", "_controller_", "_borrowed_token_", "_collateral_token_"]
    [.elem .address, .elem .address, .elem .address, .elem .address] cd = _
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWords?, Nat.zero_add,
    decodeScalarWord_calldata_address cd 0 (by decide) (by omega), decodeScalarWord_calldata_address cd 32 (by decide) (by omega),
    decodeScalarWord_calldata_address cd 64 (by decide) (by omega), decodeScalarWord_calldata_address cd 96 (by decide) (by omega)]
  by_cases h0 : (calldataWord cd 4).toNat < EVM.addressModulus <;>
    by_cases h1 : (calldataWord cd 36).toNat < EVM.addressModulus <;>
    by_cases h2 : (calldataWord cd 68).toNat < EVM.addressModulus <;>
    by_cases h3 : (calldataWord cd 100).toNat < EVM.addressModulus <;>
    simp only [h0, h1, h2, h3, ↓reduceIte, Option.bind, bind] <;> rfl

theorem vaultInitializeDecodeShort (cd : ByteArray) (hsize : 4 ≤ cd.size) (hshort : cd.size < 132) :
    config.externalABI.decodeCalldata? (initializeTransition.params.map Param.name)
      (transitionSignature initializeTransition).paramTypes cd = none := by
  change decodeCalldataWithMode .vyper ["_amm_", "_controller_", "_borrowed_token_", "_collateral_token_"]
    [.elem .address, .elem .address, .elem .address, .elem .address] cd = none
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [decodeScalarWords_none_short _ _ _ (Nat.zero_le _)
    (by simp only [List.length_cons, List.length_nil, List.length_drop, htlen]; omega)]

end Benchmarks.CurveVault
