import Benchmarks.CurveVault.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault
set_option maxRecDepth 2000
set_option maxHeartbeats 0

/-! ## Solm dispatch: which transition a selector reaches -/

theorem vaultDispatch_withdraw_uint256_address {I : ExecutionEnv} 
    (hsel : selIs I (vaultSelBytes 0)) :
    dispatchMsg contract I.calldata = some withdraw_uint256_addressTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := []) (post := [withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := withdraw_uint256_addressTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp at hu
  · rw [withdraw_uint256_addressSelectorOf]; exact hsel

theorem vaultDispatch_withdraw_uint256 {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0))
    (hsel : selIs I (vaultSelBytes 1)) :
    dispatchMsg contract I.calldata = some withdraw_uint256Transition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition]) (post := [withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := withdraw_uint256Transition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
  · rw [withdraw_uint256SelectorOf]; exact hsel

theorem vaultDispatch_withdraw_uint256_address_address {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1))
    (hsel : selIs I (vaultSelBytes 2)) :
    dispatchMsg contract I.calldata = some withdraw_uint256_address_addressTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition]) (post := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := withdraw_uint256_address_addressTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
  · rw [withdraw_uint256_address_addressSelectorOf]; exact hsel

theorem vaultDispatch_totalAssets {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2))
    (hsel : selIs I (vaultSelBytes 3)) :
    dispatchMsg contract I.calldata = some totalAssetsTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition]) (post := [nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := totalAssetsTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
  · rw [totalAssetsSelectorOf]; exact hsel

theorem vaultDispatch_name {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3))
    (hsel : selIs I (vaultSelBytes 4)) :
    dispatchMsg contract I.calldata = some nameTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition]) (post := [convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := nameTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
  · rw [nameSelectorOf]; exact hsel

theorem vaultDispatch_convertToAssets {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4))
    (hsel : selIs I (vaultSelBytes 5)) :
    dispatchMsg contract I.calldata = some convertToAssetsTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition]) (post := [approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := convertToAssetsTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
  · rw [convertToAssetsSelectorOf]; exact hsel

theorem vaultDispatch_approve {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5))
    (hsel : selIs I (vaultSelBytes 6)) :
    dispatchMsg contract I.calldata = some approveTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition]) (post := [previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := approveTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
  · rw [approveSelectorOf]; exact hsel

theorem vaultDispatch_previewWithdraw {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6))
    (hsel : selIs I (vaultSelBytes 7)) :
    dispatchMsg contract I.calldata = some previewWithdrawTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition]) (post := [totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := previewWithdrawTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
  · rw [previewWithdrawSelectorOf]; exact hsel

theorem vaultDispatch_totalSupply {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7))
    (hsel : selIs I (vaultSelBytes 8)) :
    dispatchMsg contract I.calldata = some totalSupplyTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition]) (post := [transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := totalSupplyTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
  · rw [totalSupplySelectorOf]; exact hsel

theorem vaultDispatch_transferFrom {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8))
    (hsel : selIs I (vaultSelBytes 9)) :
    dispatchMsg contract I.calldata = some transferFromTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition]) (post := [collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := transferFromTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
  · rw [transferFromSelectorOf]; exact hsel

theorem vaultDispatch_collateral_token {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9))
    (hsel : selIs I (vaultSelBytes 10)) :
    dispatchMsg contract I.calldata = some collateral_tokenTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition]) (post := [pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := collateral_tokenTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
  · rw [collateral_tokenSelectorOf]; exact hsel

theorem vaultDispatch_pricePerShare_bool {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10))
    (hsel : selIs I (vaultSelBytes 11)) :
    dispatchMsg contract I.calldata = some pricePerShare_boolTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition]) (post := [pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := pricePerShare_boolTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
  · rw [pricePerShare_boolSelectorOf]; exact hsel

theorem vaultDispatch_pricePerShare_ {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11))
    (hsel : selIs I (vaultSelBytes 12)) :
    dispatchMsg contract I.calldata = some pricePerShare_Transition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition]) (post := [ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := pricePerShare_Transition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
  · rw [pricePerShare_SelectorOf]; exact hsel

theorem vaultDispatch_amm {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12))
    (hsel : selIs I (vaultSelBytes 13)) :
    dispatchMsg contract I.calldata = some ammTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition]) (post := [decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := ammTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
  · rw [ammSelectorOf]; exact hsel

theorem vaultDispatch_decimals {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13))
    (hsel : selIs I (vaultSelBytes 14)) :
    dispatchMsg contract I.calldata = some decimalsTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition]) (post := [assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := decimalsTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
  · rw [decimalsSelectorOf]; exact hsel

theorem vaultDispatch_asset {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14))
    (hsel : selIs I (vaultSelBytes 15)) :
    dispatchMsg contract I.calldata = some assetTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition]) (post := [increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := assetTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
  · rw [assetSelectorOf]; exact hsel

theorem vaultDispatch_increaseAllowance {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15))
    (hsel : selIs I (vaultSelBytes 16)) :
    dispatchMsg contract I.calldata = some increaseAllowanceTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition]) (post := [maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := increaseAllowanceTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
  · rw [increaseAllowanceSelectorOf]; exact hsel

theorem vaultDispatch_maxDeposit {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16))
    (hsel : selIs I (vaultSelBytes 17)) :
    dispatchMsg contract I.calldata = some maxDepositTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition]) (post := [previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := maxDepositTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
  · rw [maxDepositSelectorOf]; exact hsel

theorem vaultDispatch_previewRedeem {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17))
    (hsel : selIs I (vaultSelBytes 18)) :
    dispatchMsg contract I.calldata = some previewRedeemTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition]) (post := [deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := previewRedeemTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
  · rw [previewRedeemSelectorOf]; exact hsel

theorem vaultDispatch_deposit_uint256_address {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18))
    (hsel : selIs I (vaultSelBytes 19)) :
    dispatchMsg contract I.calldata = some deposit_uint256_addressTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition]) (post := [deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := deposit_uint256_addressTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
  · rw [deposit_uint256_addressSelectorOf]; exact hsel

theorem vaultDispatch_deposit_uint256 {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19))
    (hsel : selIs I (vaultSelBytes 20)) :
    dispatchMsg contract I.calldata = some deposit_uint256Transition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition]) (post := [balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := deposit_uint256Transition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
  · rw [deposit_uint256SelectorOf]; exact hsel

theorem vaultDispatch_balanceOf {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20))
    (hsel : selIs I (vaultSelBytes 21)) :
    dispatchMsg contract I.calldata = some balanceOfTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition]) (post := [borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := balanceOfTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
  · rw [balanceOfSelectorOf]; exact hsel

theorem vaultDispatch_borrowed_token {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21))
    (hsel : selIs I (vaultSelBytes 22)) :
    dispatchMsg contract I.calldata = some borrowed_tokenTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition]) (post := [redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := borrowed_tokenTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
  · rw [borrowed_tokenSelectorOf]; exact hsel

theorem vaultDispatch_redeem_uint256_address {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22))
    (hsel : selIs I (vaultSelBytes 23)) :
    dispatchMsg contract I.calldata = some redeem_uint256_addressTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition]) (post := [redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := redeem_uint256_addressTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
  · rw [redeem_uint256_addressSelectorOf]; exact hsel

theorem vaultDispatch_redeem_uint256_address_address {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23))
    (hsel : selIs I (vaultSelBytes 24)) :
    dispatchMsg contract I.calldata = some redeem_uint256_address_addressTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition]) (post := [redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := redeem_uint256_address_addressTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
  · rw [redeem_uint256_address_addressSelectorOf]; exact hsel

theorem vaultDispatch_redeem_uint256 {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24))
    (hsel : selIs I (vaultSelBytes 25)) :
    dispatchMsg contract I.calldata = some redeem_uint256Transition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition]) (post := [set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := redeem_uint256Transition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
  · rw [redeem_uint256SelectorOf]; exact hsel

theorem vaultDispatch_set_max_supply {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25))
    (hsel : selIs I (vaultSelBytes 26)) :
    dispatchMsg contract I.calldata = some set_max_supplyTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition]) (post := [mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := set_max_supplyTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
  · rw [set_max_supplySelectorOf]; exact hsel

theorem vaultDispatch_mint_uint256_address {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26))
    (hsel : selIs I (vaultSelBytes 27)) :
    dispatchMsg contract I.calldata = some mint_uint256_addressTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition]) (post := [mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := mint_uint256_addressTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
  · rw [mint_uint256_addressSelectorOf]; exact hsel

theorem vaultDispatch_mint_uint256 {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27))
    (hsel : selIs I (vaultSelBytes 28)) :
    dispatchMsg contract I.calldata = some mint_uint256Transition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition]) (post := [symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := mint_uint256Transition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
  · rw [mint_uint256SelectorOf]; exact hsel

theorem vaultDispatch_symbol {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28))
    (hsel : selIs I (vaultSelBytes 29)) :
    dispatchMsg contract I.calldata = some symbolTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition]) (post := [decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := symbolTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
  · rw [symbolSelectorOf]; exact hsel

theorem vaultDispatch_decreaseAllowance {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29))
    (hsel : selIs I (vaultSelBytes 30)) :
    dispatchMsg contract I.calldata = some decreaseAllowanceTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition]) (post := [transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := decreaseAllowanceTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
  · rw [decreaseAllowanceSelectorOf]; exact hsel

theorem vaultDispatch_transfer {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30))
    (hsel : selIs I (vaultSelBytes 31)) :
    dispatchMsg contract I.calldata = some transferTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition]) (post := [lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := transferTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
  · rw [transferSelectorOf]; exact hsel

theorem vaultDispatch_lend_apr {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31))
    (hsel : selIs I (vaultSelBytes 32)) :
    dispatchMsg contract I.calldata = some lend_aprTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition]) (post := [previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := lend_aprTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
  · rw [lend_aprSelectorOf]; exact hsel

theorem vaultDispatch_previewMint {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32))
    (hsel : selIs I (vaultSelBytes 33)) :
    dispatchMsg contract I.calldata = some previewMintTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition]) (post := [borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := previewMintTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
  · rw [previewMintSelectorOf]; exact hsel

theorem vaultDispatch_borrow_apr {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32)) (h33 : ¬ selIs I (vaultSelBytes 33))
    (hsel : selIs I (vaultSelBytes 34)) :
    dispatchMsg contract I.calldata = some borrow_aprTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition]) (post := [factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := borrow_aprTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
  · rw [borrow_aprSelectorOf]; exact hsel

theorem vaultDispatch_factory {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32)) (h33 : ¬ selIs I (vaultSelBytes 33)) (h34 : ¬ selIs I (vaultSelBytes 34))
    (hsel : selIs I (vaultSelBytes 35)) :
    dispatchMsg contract I.calldata = some factoryTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition]) (post := [maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := factoryTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [borrow_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
  · rw [factorySelectorOf]; exact hsel

theorem vaultDispatch_maxMint {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32)) (h33 : ¬ selIs I (vaultSelBytes 33)) (h34 : ¬ selIs I (vaultSelBytes 34)) (h35 : ¬ selIs I (vaultSelBytes 35))
    (hsel : selIs I (vaultSelBytes 36)) :
    dispatchMsg contract I.calldata = some maxMintTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition]) (post := [convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := maxMintTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [borrow_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [factorySelectorOf]; exact Bool.eq_false_of_not_eq_true h35
  · rw [maxMintSelectorOf]; exact hsel

theorem vaultDispatch_convertToShares {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32)) (h33 : ¬ selIs I (vaultSelBytes 33)) (h34 : ¬ selIs I (vaultSelBytes 34)) (h35 : ¬ selIs I (vaultSelBytes 35)) (h36 : ¬ selIs I (vaultSelBytes 36))
    (hsel : selIs I (vaultSelBytes 37)) :
    dispatchMsg contract I.calldata = some convertToSharesTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition]) (post := [maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := convertToSharesTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [borrow_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [factorySelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
  · rw [convertToSharesSelectorOf]; exact hsel

theorem vaultDispatch_maxWithdraw {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32)) (h33 : ¬ selIs I (vaultSelBytes 33)) (h34 : ¬ selIs I (vaultSelBytes 34)) (h35 : ¬ selIs I (vaultSelBytes 35)) (h36 : ¬ selIs I (vaultSelBytes 36)) (h37 : ¬ selIs I (vaultSelBytes 37))
    (hsel : selIs I (vaultSelBytes 38)) :
    dispatchMsg contract I.calldata = some maxWithdrawTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition]) (post := [maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := maxWithdrawTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [borrow_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [factorySelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [convertToSharesSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
  · rw [maxWithdrawSelectorOf]; exact hsel

theorem vaultDispatch_maxSupply {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32)) (h33 : ¬ selIs I (vaultSelBytes 33)) (h34 : ¬ selIs I (vaultSelBytes 34)) (h35 : ¬ selIs I (vaultSelBytes 35)) (h36 : ¬ selIs I (vaultSelBytes 36)) (h37 : ¬ selIs I (vaultSelBytes 37)) (h38 : ¬ selIs I (vaultSelBytes 38))
    (hsel : selIs I (vaultSelBytes 39)) :
    dispatchMsg contract I.calldata = some maxSupplyTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition]) (post := [maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := maxSupplyTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [borrow_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [factorySelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [convertToSharesSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
  · rw [maxSupplySelectorOf]; exact hsel

theorem vaultDispatch_maxRedeem {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32)) (h33 : ¬ selIs I (vaultSelBytes 33)) (h34 : ¬ selIs I (vaultSelBytes 34)) (h35 : ¬ selIs I (vaultSelBytes 35)) (h36 : ¬ selIs I (vaultSelBytes 36)) (h37 : ¬ selIs I (vaultSelBytes 37)) (h38 : ¬ selIs I (vaultSelBytes 38)) (h39 : ¬ selIs I (vaultSelBytes 39))
    (hsel : selIs I (vaultSelBytes 40)) :
    dispatchMsg contract I.calldata = some maxRedeemTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition]) (post := [allowanceTransition, previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := maxRedeemTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [borrow_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [factorySelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [convertToSharesSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [maxSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h39
  · rw [maxRedeemSelectorOf]; exact hsel

theorem vaultDispatch_allowance {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32)) (h33 : ¬ selIs I (vaultSelBytes 33)) (h34 : ¬ selIs I (vaultSelBytes 34)) (h35 : ¬ selIs I (vaultSelBytes 35)) (h36 : ¬ selIs I (vaultSelBytes 36)) (h37 : ¬ selIs I (vaultSelBytes 37)) (h38 : ¬ selIs I (vaultSelBytes 38)) (h39 : ¬ selIs I (vaultSelBytes 39)) (h40 : ¬ selIs I (vaultSelBytes 40))
    (hsel : selIs I (vaultSelBytes 41)) :
    dispatchMsg contract I.calldata = some allowanceTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition]) (post := [previewDepositTransition, controllerTransition, adminTransition, initializeTransition])
    (ti := allowanceTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [borrow_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [factorySelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [convertToSharesSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [maxSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
  · rw [allowanceSelectorOf]; exact hsel

theorem vaultDispatch_previewDeposit {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32)) (h33 : ¬ selIs I (vaultSelBytes 33)) (h34 : ¬ selIs I (vaultSelBytes 34)) (h35 : ¬ selIs I (vaultSelBytes 35)) (h36 : ¬ selIs I (vaultSelBytes 36)) (h37 : ¬ selIs I (vaultSelBytes 37)) (h38 : ¬ selIs I (vaultSelBytes 38)) (h39 : ¬ selIs I (vaultSelBytes 39)) (h40 : ¬ selIs I (vaultSelBytes 40)) (h41 : ¬ selIs I (vaultSelBytes 41))
    (hsel : selIs I (vaultSelBytes 42)) :
    dispatchMsg contract I.calldata = some previewDepositTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition]) (post := [controllerTransition, adminTransition, initializeTransition])
    (ti := previewDepositTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [borrow_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [factorySelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [convertToSharesSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [maxSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
  · rw [previewDepositSelectorOf]; exact hsel

theorem vaultDispatch_controller {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32)) (h33 : ¬ selIs I (vaultSelBytes 33)) (h34 : ¬ selIs I (vaultSelBytes 34)) (h35 : ¬ selIs I (vaultSelBytes 35)) (h36 : ¬ selIs I (vaultSelBytes 36)) (h37 : ¬ selIs I (vaultSelBytes 37)) (h38 : ¬ selIs I (vaultSelBytes 38)) (h39 : ¬ selIs I (vaultSelBytes 39)) (h40 : ¬ selIs I (vaultSelBytes 40)) (h41 : ¬ selIs I (vaultSelBytes 41)) (h42 : ¬ selIs I (vaultSelBytes 42))
    (hsel : selIs I (vaultSelBytes 43)) :
    dispatchMsg contract I.calldata = some controllerTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition]) (post := [adminTransition, initializeTransition])
    (ti := controllerTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [borrow_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [factorySelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [convertToSharesSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [maxSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [previewDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
  · rw [controllerSelectorOf]; exact hsel

theorem vaultDispatch_admin {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32)) (h33 : ¬ selIs I (vaultSelBytes 33)) (h34 : ¬ selIs I (vaultSelBytes 34)) (h35 : ¬ selIs I (vaultSelBytes 35)) (h36 : ¬ selIs I (vaultSelBytes 36)) (h37 : ¬ selIs I (vaultSelBytes 37)) (h38 : ¬ selIs I (vaultSelBytes 38)) (h39 : ¬ selIs I (vaultSelBytes 39)) (h40 : ¬ selIs I (vaultSelBytes 40)) (h41 : ¬ selIs I (vaultSelBytes 41)) (h42 : ¬ selIs I (vaultSelBytes 42)) (h43 : ¬ selIs I (vaultSelBytes 43))
    (hsel : selIs I (vaultSelBytes 44)) :
    dispatchMsg contract I.calldata = some adminTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition]) (post := [initializeTransition])
    (ti := adminTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [borrow_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [factorySelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [convertToSharesSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [maxSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [previewDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [controllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
  · rw [adminSelectorOf]; exact hsel

theorem vaultDispatch_initialize {I : ExecutionEnv} (h0 : ¬ selIs I (vaultSelBytes 0)) (h1 : ¬ selIs I (vaultSelBytes 1)) (h2 : ¬ selIs I (vaultSelBytes 2)) (h3 : ¬ selIs I (vaultSelBytes 3)) (h4 : ¬ selIs I (vaultSelBytes 4)) (h5 : ¬ selIs I (vaultSelBytes 5)) (h6 : ¬ selIs I (vaultSelBytes 6)) (h7 : ¬ selIs I (vaultSelBytes 7)) (h8 : ¬ selIs I (vaultSelBytes 8)) (h9 : ¬ selIs I (vaultSelBytes 9)) (h10 : ¬ selIs I (vaultSelBytes 10)) (h11 : ¬ selIs I (vaultSelBytes 11)) (h12 : ¬ selIs I (vaultSelBytes 12)) (h13 : ¬ selIs I (vaultSelBytes 13)) (h14 : ¬ selIs I (vaultSelBytes 14)) (h15 : ¬ selIs I (vaultSelBytes 15)) (h16 : ¬ selIs I (vaultSelBytes 16)) (h17 : ¬ selIs I (vaultSelBytes 17)) (h18 : ¬ selIs I (vaultSelBytes 18)) (h19 : ¬ selIs I (vaultSelBytes 19)) (h20 : ¬ selIs I (vaultSelBytes 20)) (h21 : ¬ selIs I (vaultSelBytes 21)) (h22 : ¬ selIs I (vaultSelBytes 22)) (h23 : ¬ selIs I (vaultSelBytes 23)) (h24 : ¬ selIs I (vaultSelBytes 24)) (h25 : ¬ selIs I (vaultSelBytes 25)) (h26 : ¬ selIs I (vaultSelBytes 26)) (h27 : ¬ selIs I (vaultSelBytes 27)) (h28 : ¬ selIs I (vaultSelBytes 28)) (h29 : ¬ selIs I (vaultSelBytes 29)) (h30 : ¬ selIs I (vaultSelBytes 30)) (h31 : ¬ selIs I (vaultSelBytes 31)) (h32 : ¬ selIs I (vaultSelBytes 32)) (h33 : ¬ selIs I (vaultSelBytes 33)) (h34 : ¬ selIs I (vaultSelBytes 34)) (h35 : ¬ selIs I (vaultSelBytes 35)) (h36 : ¬ selIs I (vaultSelBytes 36)) (h37 : ¬ selIs I (vaultSelBytes 37)) (h38 : ¬ selIs I (vaultSelBytes 38)) (h39 : ¬ selIs I (vaultSelBytes 39)) (h40 : ¬ selIs I (vaultSelBytes 40)) (h41 : ¬ selIs I (vaultSelBytes 41)) (h42 : ¬ selIs I (vaultSelBytes 42)) (h43 : ¬ selIs I (vaultSelBytes 43)) (h44 : ¬ selIs I (vaultSelBytes 44))
    (hsel : selIs I (vaultSelBytes 45)) :
    dispatchMsg contract I.calldata = some initializeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [withdraw_uint256_addressTransition, withdraw_uint256Transition, withdraw_uint256_address_addressTransition, totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, totalSupplyTransition, transferFromTransition, collateral_tokenTransition, pricePerShare_boolTransition, pricePerShare_Transition, ammTransition, decimalsTransition, assetTransition, increaseAllowanceTransition, maxDepositTransition, previewRedeemTransition, deposit_uint256_addressTransition, deposit_uint256Transition, balanceOfTransition, borrowed_tokenTransition, redeem_uint256_addressTransition, redeem_uint256_address_addressTransition, redeem_uint256Transition, set_max_supplyTransition, mint_uint256_addressTransition, mint_uint256Transition, symbolTransition, decreaseAllowanceTransition, transferTransition, lend_aprTransition, previewMintTransition, borrow_aprTransition, factoryTransition, maxMintTransition, convertToSharesTransition, maxWithdrawTransition, maxSupplyTransition, maxRedeemTransition, allowanceTransition, previewDepositTransition, controllerTransition, adminTransition]) (post := [])
    (ti := initializeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [withdraw_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [withdraw_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [withdraw_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [collateral_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [pricePerShare_boolSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [pricePerShare_SelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [ammSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [increaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [deposit_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [deposit_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [borrowed_tokenSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [redeem_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [redeem_uint256_address_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [redeem_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [set_max_supplySelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [mint_uint256_addressSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [mint_uint256SelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [decreaseAllowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [lend_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [borrow_aprSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [factorySelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [convertToSharesSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [maxSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [previewDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [controllerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [adminSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
  · rw [initializeSelectorOf]; exact hsel

theorem vaultDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd, transitions_eq]
  refine dispatchList_none_short _ ?_ h
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [withdraw_uint256_addressSelectorOf]; rfl
  · rw [withdraw_uint256SelectorOf]; rfl
  · rw [withdraw_uint256_address_addressSelectorOf]; rfl
  · rw [totalAssetsSelectorOf]; rfl
  · rw [nameSelectorOf]; rfl
  · rw [convertToAssetsSelectorOf]; rfl
  · rw [approveSelectorOf]; rfl
  · rw [previewWithdrawSelectorOf]; rfl
  · rw [totalSupplySelectorOf]; rfl
  · rw [transferFromSelectorOf]; rfl
  · rw [collateral_tokenSelectorOf]; rfl
  · rw [pricePerShare_boolSelectorOf]; rfl
  · rw [pricePerShare_SelectorOf]; rfl
  · rw [ammSelectorOf]; rfl
  · rw [decimalsSelectorOf]; rfl
  · rw [assetSelectorOf]; rfl
  · rw [increaseAllowanceSelectorOf]; rfl
  · rw [maxDepositSelectorOf]; rfl
  · rw [previewRedeemSelectorOf]; rfl
  · rw [deposit_uint256_addressSelectorOf]; rfl
  · rw [deposit_uint256SelectorOf]; rfl
  · rw [balanceOfSelectorOf]; rfl
  · rw [borrowed_tokenSelectorOf]; rfl
  · rw [redeem_uint256_addressSelectorOf]; rfl
  · rw [redeem_uint256_address_addressSelectorOf]; rfl
  · rw [redeem_uint256SelectorOf]; rfl
  · rw [set_max_supplySelectorOf]; rfl
  · rw [mint_uint256_addressSelectorOf]; rfl
  · rw [mint_uint256SelectorOf]; rfl
  · rw [symbolSelectorOf]; rfl
  · rw [decreaseAllowanceSelectorOf]; rfl
  · rw [transferSelectorOf]; rfl
  · rw [lend_aprSelectorOf]; rfl
  · rw [previewMintSelectorOf]; rfl
  · rw [borrow_aprSelectorOf]; rfl
  · rw [factorySelectorOf]; rfl
  · rw [maxMintSelectorOf]; rfl
  · rw [convertToSharesSelectorOf]; rfl
  · rw [maxWithdrawSelectorOf]; rfl
  · rw [maxSupplySelectorOf]; rfl
  · rw [maxRedeemSelectorOf]; rfl
  · rw [allowanceSelectorOf]; rfl
  · rw [previewDepositSelectorOf]; rfl
  · rw [controllerSelectorOf]; rfl
  · rw [adminSelectorOf]; rfl
  · rw [initializeSelectorOf]; rfl

theorem vaultDispatch_none_nomatch {I : ExecutionEnv}
    (hnm : ∀ i, i < 46 → (vaultSelBytes i == I.calldata.extract 0 4) = false) :
    dispatchMsg contract I.calldata = none := by
  refine dispatchMsg_none_of_all_ne (contract := contract) (cd := I.calldata) (by rfl) (by rfl) ?_
  intro t ht
  rw [transitions_eq] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [withdraw_uint256_addressSelectorOf]; exact hnm 0 (by omega)
  · rw [withdraw_uint256SelectorOf]; exact hnm 1 (by omega)
  · rw [withdraw_uint256_address_addressSelectorOf]; exact hnm 2 (by omega)
  · rw [totalAssetsSelectorOf]; exact hnm 3 (by omega)
  · rw [nameSelectorOf]; exact hnm 4 (by omega)
  · rw [convertToAssetsSelectorOf]; exact hnm 5 (by omega)
  · rw [approveSelectorOf]; exact hnm 6 (by omega)
  · rw [previewWithdrawSelectorOf]; exact hnm 7 (by omega)
  · rw [totalSupplySelectorOf]; exact hnm 8 (by omega)
  · rw [transferFromSelectorOf]; exact hnm 9 (by omega)
  · rw [collateral_tokenSelectorOf]; exact hnm 10 (by omega)
  · rw [pricePerShare_boolSelectorOf]; exact hnm 11 (by omega)
  · rw [pricePerShare_SelectorOf]; exact hnm 12 (by omega)
  · rw [ammSelectorOf]; exact hnm 13 (by omega)
  · rw [decimalsSelectorOf]; exact hnm 14 (by omega)
  · rw [assetSelectorOf]; exact hnm 15 (by omega)
  · rw [increaseAllowanceSelectorOf]; exact hnm 16 (by omega)
  · rw [maxDepositSelectorOf]; exact hnm 17 (by omega)
  · rw [previewRedeemSelectorOf]; exact hnm 18 (by omega)
  · rw [deposit_uint256_addressSelectorOf]; exact hnm 19 (by omega)
  · rw [deposit_uint256SelectorOf]; exact hnm 20 (by omega)
  · rw [balanceOfSelectorOf]; exact hnm 21 (by omega)
  · rw [borrowed_tokenSelectorOf]; exact hnm 22 (by omega)
  · rw [redeem_uint256_addressSelectorOf]; exact hnm 23 (by omega)
  · rw [redeem_uint256_address_addressSelectorOf]; exact hnm 24 (by omega)
  · rw [redeem_uint256SelectorOf]; exact hnm 25 (by omega)
  · rw [set_max_supplySelectorOf]; exact hnm 26 (by omega)
  · rw [mint_uint256_addressSelectorOf]; exact hnm 27 (by omega)
  · rw [mint_uint256SelectorOf]; exact hnm 28 (by omega)
  · rw [symbolSelectorOf]; exact hnm 29 (by omega)
  · rw [decreaseAllowanceSelectorOf]; exact hnm 30 (by omega)
  · rw [transferSelectorOf]; exact hnm 31 (by omega)
  · rw [lend_aprSelectorOf]; exact hnm 32 (by omega)
  · rw [previewMintSelectorOf]; exact hnm 33 (by omega)
  · rw [borrow_aprSelectorOf]; exact hnm 34 (by omega)
  · rw [factorySelectorOf]; exact hnm 35 (by omega)
  · rw [maxMintSelectorOf]; exact hnm 36 (by omega)
  · rw [convertToSharesSelectorOf]; exact hnm 37 (by omega)
  · rw [maxWithdrawSelectorOf]; exact hnm 38 (by omega)
  · rw [maxSupplySelectorOf]; exact hnm 39 (by omega)
  · rw [maxRedeemSelectorOf]; exact hnm 40 (by omega)
  · rw [allowanceSelectorOf]; exact hnm 41 (by omega)
  · rw [previewDepositSelectorOf]; exact hnm 42 (by omega)
  · rw [controllerSelectorOf]; exact hnm 43 (by omega)
  · rw [adminSelectorOf]; exact hnm 44 (by omega)
  · rw [initializeSelectorOf]; exact hnm 45 (by omega)

end Benchmarks.CurveVault
