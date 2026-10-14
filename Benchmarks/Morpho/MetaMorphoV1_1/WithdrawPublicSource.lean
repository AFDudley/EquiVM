import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawInternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.DepositFinishSource
import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedFeeSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertSharesUpSource
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalCalls

/-! Public withdrawal source composition with upward share conversion. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def withdrawPublicLocals (assets : UInt256) (receiver owner : AccountAddress) : Store :=
  (((∅ : Store).insert "assets" (uint256Value assets)).insert "receiver" (.address receiver)).insert
    "owner" (.address owner)

def withdrawPublicFrame (evm : State) (imms : Store) (assets : UInt256)
    (receiver owner : AccountAddress) : Frame :=
  ⟨contract, (((withdrawPublicLocals assets receiver owner).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).insert cursorName (uint256Value ⟨128⟩)).insert
      "shares" (uint256Value ⟨0⟩), imms⟩

def withdrawPublicAccruedFrame (evm : State) (imms : Store) (assets : UInt256)
    (receiver owner : AccountAddress) (cursor : UInt256) : Frame :=
  let f := withdrawPublicFrame evm imms assets receiver owner
  { f with locals := f.locals.insert cursorName (uint256Value cursor) }

def withdrawPublicSupplyFrame (evm evm' : State) (imms : Store) (assets : UInt256)
    (receiver owner : AccountAddress) (cursor : UInt256) : Frame :=
  let f := withdrawPublicAccruedFrame evm imms assets receiver owner cursor
  { f with locals := f.locals.insert "__c1" (uint256Value
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)) }

def withdrawPublicReadyFrame (frame : Frame) (shares : UInt256) (caller : AccountAddress) : Frame :=
  { frame with locals := ((frame.locals.insert "__c2" (uint256Value shares)).insert
      "shares" (uint256Value shares)).insert "__c3" (.address caller) }

def withdrawPublicFinish : List Stmt :=
  [.internalCall allocatedWithdrawFunction.name
    [.var "__c3", .var "receiver", .var "owner", .var "assets", .var "shares", .var cursorName] "__c4",
   .return [.var "shares"]]

def withdrawPublicConversion : List Stmt :=
  [.internalCall "totalSupply_body" [] "__c1",
   .internalCall "_convertToSharesWithTotals"
     [.var "assets", .var "__c1", .storage ⟨"lastTotalAssets", []⟩, .intLit 1] "__c2",
   .assign .localVar ⟨"shares", []⟩ (.var "__c2"),
   .internalCall "_msgSender" [] "__c3"] ++ withdrawPublicFinish

def withdrawPublicAccrual : List Stmt :=
  .internalCall allocatedAccrueInterestFunction.name [.var cursorName] cursorName ::
    withdrawPublicConversion

theorem withdrawPublicPrefix (evm : State) (imms : Store) (assets : UInt256)
    (receiver owner : AccountAddress) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, withdrawPublicLocals assets receiver owner, imms⟩
      withdrawTransition.body (withdrawPublicFrame evm imms assets receiver owner) withdrawPublicAccrual := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨128⟩)
    (by simp only [evalExpr?, pure]; rfl))
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl)) htail

theorem withdrawPublicAccrualArgs (evm : State) (imms : Store) (assets : UInt256)
    (receiver owner : AccountAddress) :
    evalExprs? config (withdrawPublicFrame evm imms assets receiver owner) evm [.var cursorName] =
      .ok [uint256Value ⟨128⟩] := by
  simp only [evalExprs?, evalExpr?, withdrawPublicFrame,
    store_get_ne _ _ (by decide : ("shares" == cursorName) = false), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem withdrawPublicAccrualReverts {evm : State} {imms : Store} {assets : UInt256}
    {receiver owner : AccountAddress}
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body .reverted) :
    ExecBlock config (withdrawPublicFrame evm imms assets receiver owner) evm withdrawPublicAccrual .reverted := by
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (callee := allocatedAccrueInterestFunction)
    (withdrawPublicAccrualArgs evm imms assets receiver owner) rfl rfl hbody)

theorem withdrawPublicAccrualStatic {evm : State} {imms : Store} {assets : UInt256}
    {receiver owner : AccountAddress}
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body .staticViolation) :
    ExecBlock config (withdrawPublicFrame evm imms assets receiver owner) evm
      withdrawPublicAccrual .staticViolation := by
  exact ExecBlock.consStatic (ExecStmt.internalCallStatic
    (callee := allocatedAccrueInterestFunction.toCallable)
    (withdrawPublicAccrualArgs evm imms assets receiver owner) rfl rfl hbody)

theorem withdrawPublicAccrualContinue {evm evm' : State} {imms : Store} {assets cursor : UInt256}
    {receiver owner : AccountAddress} {final : Frame} {result : ExecResult}
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body (.returned final evm' (some [uint256Value cursor])))
    (htail : ExecBlock config (withdrawPublicAccruedFrame evm imms assets receiver owner cursor) evm'
      withdrawPublicConversion result) :
    ExecBlock config (withdrawPublicFrame evm imms assets receiver owner) evm withdrawPublicAccrual result := by
  exact ExecBlock.consNormal (internalCallFunctionReturn
    (callee := allocatedAccrueInterestFunction)
    (withdrawPublicAccrualArgs evm imms assets receiver owner) rfl rfl hbody) htail

theorem withdrawPublicConversionArgs (evm evm' : State) (imms : Store) (assets : UInt256)
    (receiver owner : AccountAddress) (cursor : UInt256) :
    evalExprs? config (withdrawPublicSupplyFrame evm evm' imms assets receiver owner cursor) evm'
      [.var "assets", .var "__c1", .storage ⟨"lastTotalAssets", []⟩, .intLit 1] =
      .ok [uint256Value assets,
        uint256Value (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩),
        uint256Value (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩),
        uint256Value ⟨1⟩] := by
  have hn : (withdrawPublicSupplyFrame evm evm' imms assets receiver owner cursor).locals.get?
      "lastTotalAssets" = none := by
    simp [withdrawPublicSupplyFrame, withdrawPublicAccruedFrame, withdrawPublicFrame, withdrawPublicLocals, cursorName]
  have ht := depositLastAssetsSource (frame :=
    withdrawPublicSupplyFrame evm evm' imms assets receiver owner cursor) (evm := evm') rfl hn
  simp only [evalExprs?, ht]
  simp only [evalExpr?, withdrawPublicSupplyFrame, withdrawPublicAccruedFrame,
    withdrawPublicFrame, withdrawPublicLocals, store_get_self]
  repeat rw [store_get_ne _ _ (by decide)]
  simp only [store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

theorem withdrawPublicConversionReverts (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} {assets cursor : UInt256} {receiver owner : AccountAddress}
    (hbad : ¬ convertSharesUpFits v.DECIMALS_OFFSET assets
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩)) :
    ExecBlock config (withdrawPublicAccruedFrame evm (immStore v) assets receiver owner cursor) evm'
      withdrawPublicConversion .reverted := by
  exact ExecBlock.consNormal (totalSupplyInternalCall _ _ _ "__c1")
    (ExecBlock.consRevert (convertSharesUpCallReverts v
      (withdrawPublicConversionArgs evm evm' (immStore v) assets receiver owner cursor) hbad))

theorem withdrawPublicConversionPrefix (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} {assets cursor : UInt256} {receiver owner : AccountAddress}
    (hfit : convertSharesUpFits v.DECIMALS_OFFSET assets
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩)) :
    ABlock config evm' (withdrawPublicAccruedFrame evm (immStore v) assets receiver owner cursor)
      withdrawPublicConversion
      (withdrawPublicReadyFrame (withdrawPublicSupplyFrame evm evm' (immStore v) assets receiver owner cursor)
        (convertSharesUpWord v.DECIMALS_OFFSET assets
          (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)
          (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩)) evm'.executionEnv.source)
      withdrawPublicFinish := by
  constructor
  intro result htail
  apply ExecBlock.consNormal (totalSupplyInternalCall _ _ _ "__c1")
  apply ExecBlock.consNormal (convertSharesUpCall v
    (withdrawPublicConversionArgs evm evm' (immStore v) assets receiver owner cursor) hfit)
  apply ExecBlock.consNormal (ExecStmt.assign (evalLocalValue (store_get_self ..))
    (assignLocalValue (old := uint256Value ⟨0⟩) ?_))
  · exact ExecBlock.consNormal (msgSenderCall _ _ _ "__c3") htail
  · simp only [withdrawPublicSupplyFrame, withdrawPublicAccruedFrame, withdrawPublicFrame]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self ..

theorem withdrawPublicInternalArgs (evm0 evm : State) (imms : Store) (shares assets cursor : UInt256)
    (receiver owner caller : AccountAddress) :
    evalExprs? config
      (withdrawPublicReadyFrame (withdrawPublicSupplyFrame evm0 evm imms assets receiver owner cursor)
        shares caller) evm
      [.var "__c3", .var "receiver", .var "owner", .var "assets", .var "shares", .var cursorName] =
      .ok [.address caller, .address receiver, .address owner, uint256Value assets, uint256Value shares,
        uint256Value cursor] := by
  simp only [evalExprs?, evalExpr?, withdrawPublicReadyFrame, withdrawPublicSupplyFrame, withdrawPublicAccruedFrame,
    withdrawPublicFrame, withdrawPublicLocals]
  repeat first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]
  simp only [EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem withdrawPublicInternalReverts {evm0 evm : State} {imms : Store}
    {shares assets cursor : UInt256} {receiver owner : AccountAddress}
    (hbody : ExecFuncBody config
      (erc4626WithdrawFrame imms evm.executionEnv.source receiver owner assets shares cursor) evm
      allocatedWithdrawFunction.body .reverted) :
    ExecBlock config
      (withdrawPublicReadyFrame (withdrawPublicSupplyFrame evm0 evm imms assets receiver owner cursor)
        shares evm.executionEnv.source) evm withdrawPublicFinish .reverted := by
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedWithdrawFunction)
    (withdrawPublicInternalArgs evm0 evm imms shares assets cursor receiver owner evm.executionEnv.source)
    rfl rfl hbody)

theorem withdrawPublicInternalReturns {evm0 evm evm' : State} {imms : Store}
    {shares assets cursor cursor' : UInt256} {receiver owner : AccountAddress} {final : Frame}
    (hbody : ExecFuncBody config
      (erc4626WithdrawFrame imms evm.executionEnv.source receiver owner assets shares cursor) evm
      allocatedWithdrawFunction.body (.returned final evm' (some [uint256Value cursor']))) :
    ExecBlock config
      (withdrawPublicReadyFrame (withdrawPublicSupplyFrame evm0 evm imms assets receiver owner cursor)
        shares evm.executionEnv.source) evm withdrawPublicFinish
      (.returned (resumeAfterInternalCall
        (withdrawPublicReadyFrame (withdrawPublicSupplyFrame evm0 evm imms assets receiver owner cursor)
          shares evm.executionEnv.source) "__c4" (some [uint256Value cursor']))
        evm' (some [uint256Value shares])) := by
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := allocatedWithdrawFunction)
    (withdrawPublicInternalArgs evm0 evm imms shares assets cursor receiver owner evm.executionEnv.source)
    rfl rfl hbody)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, withdrawPublicReadyFrame,
    store_get_ne _ _ (by decide : ("__c4" == "shares") = false),
    store_get_ne _ _ (by decide : ("__c3" == "shares") = false), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
