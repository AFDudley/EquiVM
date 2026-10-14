import Benchmarks.Morpho.MetaMorphoV1_1.DepositInternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedFeeSource
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalCalls

/-! Source composition of public deposit: accrue, convert, deposit, and return shares. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def depositPublicLocals (assets : UInt256) (receiver : AccountAddress) : Store :=
  ((∅ : Store).insert "assets" (uint256Value assets)).insert "receiver" (.address receiver)

def depositPublicFrame (evm : State) (imms : Store) (assets : UInt256)
    (receiver : AccountAddress) : Frame :=
  ⟨contract, (((depositPublicLocals assets receiver).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).insert cursorName (uint256Value ⟨128⟩)).insert
      "shares" (uint256Value ⟨0⟩), imms⟩

def depositPublicAccruedFrame (evm : State) (imms : Store) (assets : UInt256)
    (receiver : AccountAddress) (cursor : UInt256) : Frame :=
  let f := depositPublicFrame evm imms assets receiver
  { f with locals := f.locals.insert cursorName (uint256Value cursor) }

def depositPublicSupplyFrame (evm evm' : State) (imms : Store) (assets : UInt256)
    (receiver : AccountAddress) (cursor : UInt256) : Frame :=
  let f := depositPublicAccruedFrame evm imms assets receiver cursor
  { f with locals := f.locals.insert "__c1" (uint256Value
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)) }

def depositPublicConvertFrame (frame : Frame) (shares : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "__c2" (uint256Value shares) }

def depositPublicSharesFrame (frame : Frame) (shares : UInt256) : Frame :=
  let f := depositPublicConvertFrame frame shares
  { f with locals := f.locals.insert "shares" (uint256Value shares) }

def depositPublicCallerFrame (frame : Frame) (shares : UInt256) (caller : AccountAddress) : Frame :=
  let f := depositPublicSharesFrame frame shares
  { f with locals := f.locals.insert "__c3" (.address caller) }

def depositPublicFinish : List Stmt :=
  [.internalCall allocatedDepositFunction.name
    [.var "__c3", .var "receiver", .var "assets", .var "shares", .var cursorName] "__c4",
   .return [.var "shares"]]

def depositPublicConversion : List Stmt :=
  [.internalCall "totalSupply_body" [] "__c1",
   .internalCall "_convertToSharesWithTotals"
     [.var "assets", .var "__c1", .storage ⟨"lastTotalAssets", []⟩, .intLit 0] "__c2",
   .assign .localVar ⟨"shares", []⟩ (.var "__c2"),
   .internalCall "_msgSender" [] "__c3"] ++ depositPublicFinish

def depositPublicAccrual : List Stmt :=
  .internalCall allocatedAccrueInterestFunction.name [.var cursorName] cursorName ::
    depositPublicConversion

theorem depositPublicPrefix (evm : State) (imms : Store) (assets : UInt256)
    (receiver : AccountAddress) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, depositPublicLocals assets receiver, imms⟩
      depositTransition.body (depositPublicFrame evm imms assets receiver) depositPublicAccrual := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨128⟩)
    (by simp only [evalExpr?, pure]; rfl))
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl)) htail

theorem depositPublicAccrualArgs (evm : State) (imms : Store) (assets : UInt256)
    (receiver : AccountAddress) :
    evalExprs? config (depositPublicFrame evm imms assets receiver) evm [.var cursorName] =
      .ok [uint256Value ⟨128⟩] := by
  simp only [evalExprs?, evalExpr?, depositPublicFrame,
    store_get_ne _ _ (by decide : ("shares" == cursorName) = false), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem depositPublicAccrualReverts {evm : State} {imms : Store} {assets : UInt256}
    {receiver : AccountAddress}
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body .reverted) :
    ExecBlock config (depositPublicFrame evm imms assets receiver) evm
      depositPublicAccrual .reverted := by
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (callee := allocatedAccrueInterestFunction)
    (depositPublicAccrualArgs evm imms assets receiver) rfl rfl hbody)

theorem depositPublicAccrualStatic {evm : State} {imms : Store} {assets : UInt256}
    {receiver : AccountAddress}
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body .staticViolation) :
    ExecBlock config (depositPublicFrame evm imms assets receiver) evm
      depositPublicAccrual .staticViolation := by
  exact ExecBlock.consStatic (ExecStmt.internalCallStatic
    (callee := allocatedAccrueInterestFunction.toCallable)
    (depositPublicAccrualArgs evm imms assets receiver) rfl rfl hbody)

theorem depositPublicAccrualContinue {evm evm' : State} {imms : Store} {assets cursor : UInt256}
    {receiver : AccountAddress} {final : Frame} {result : ExecResult}
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body (.returned final evm' (some [uint256Value cursor])))
    (htail : ExecBlock config (depositPublicAccruedFrame evm imms assets receiver cursor) evm'
      depositPublicConversion result) :
    ExecBlock config (depositPublicFrame evm imms assets receiver) evm
      depositPublicAccrual result := by
  exact ExecBlock.consNormal (internalCallFunctionReturn
    (callee := allocatedAccrueInterestFunction)
    (depositPublicAccrualArgs evm imms assets receiver) rfl rfl hbody) htail

theorem depositPublicConversionArgs (evm evm' : State) (imms : Store) (assets : UInt256)
    (receiver : AccountAddress) (cursor : UInt256) :
    evalExprs? config (depositPublicSupplyFrame evm evm' imms assets receiver cursor) evm'
      [.var "assets", .var "__c1", .storage ⟨"lastTotalAssets", []⟩, .intLit 0] =
      .ok [uint256Value assets,
        uint256Value (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩),
        uint256Value (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩),
        uint256Value ⟨0⟩] := by
  have hn : (depositPublicSupplyFrame evm evm' imms assets receiver cursor).locals.get?
      "lastTotalAssets" = none := by
    simp [depositPublicSupplyFrame, depositPublicAccruedFrame, depositPublicFrame,
      depositPublicLocals, cursorName]
  have ht := depositLastAssetsSource (frame :=
    depositPublicSupplyFrame evm evm' imms assets receiver cursor) (evm := evm') rfl hn
  simp only [evalExprs?, ht]
  simp only [evalExpr?, depositPublicSupplyFrame, depositPublicAccruedFrame,
    depositPublicFrame, depositPublicLocals, store_get_self]
  repeat rw [store_get_ne _ _ (by decide)]
  simp only [store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

theorem depositPublicConversionReverts (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} {assets cursor : UInt256} {receiver : AccountAddress}
    (hbad : ¬ convertSharesFits v.DECIMALS_OFFSET assets
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩)) :
    ExecBlock config (depositPublicAccruedFrame evm (immStore v) assets receiver cursor) evm'
      depositPublicConversion .reverted := by
  exact ExecBlock.consNormal (totalSupplyInternalCall _ _ _ "__c1")
    (ExecBlock.consRevert (convertSharesCallReverts v
      (depositPublicConversionArgs evm evm' (immStore v) assets receiver cursor) hbad))

theorem depositPublicConversionContinue (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} {assets cursor : UInt256} {receiver : AccountAddress} {result : ExecResult}
    (hfit : convertSharesFits v.DECIMALS_OFFSET assets
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩))
    (htail : ExecBlock config
      (depositPublicCallerFrame (depositPublicSupplyFrame evm evm' (immStore v) assets receiver cursor)
        (convertSharesWord v.DECIMALS_OFFSET assets
          (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)
          (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩)) evm'.executionEnv.source)
      evm' depositPublicFinish result) :
    ExecBlock config (depositPublicAccruedFrame evm (immStore v) assets receiver cursor) evm'
      depositPublicConversion result := by
  apply ExecBlock.consNormal (totalSupplyInternalCall _ _ _ "__c1")
  apply ExecBlock.consNormal (convertSharesCall v
    (depositPublicConversionArgs evm evm' (immStore v) assets receiver cursor) hfit)
  apply ExecBlock.consNormal (ExecStmt.assign (evalLocalValue (store_get_self ..))
    (assignLocalValue (old := uint256Value ⟨0⟩) ?_))
  · exact ExecBlock.consNormal (msgSenderCall _ _ _ "__c3") htail
  · simp only [depositPublicSupplyFrame, depositPublicAccruedFrame, depositPublicFrame]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self ..

theorem depositPublicInternalArgs (evm0 evm : State) (imms : Store) (assets shares cursor : UInt256)
    (receiver caller : AccountAddress) :
    evalExprs? config
      (depositPublicCallerFrame (depositPublicSupplyFrame evm0 evm imms assets receiver cursor)
        shares caller) evm
      [.var "__c3", .var "receiver", .var "assets", .var "shares", .var cursorName] =
      .ok [.address caller, .address receiver, uint256Value assets, uint256Value shares,
        uint256Value cursor] := by
  simp only [evalExprs?, evalExpr?, depositPublicCallerFrame, depositPublicSharesFrame,
    depositPublicConvertFrame, depositPublicSupplyFrame, depositPublicAccruedFrame,
    depositPublicFrame, depositPublicLocals]
  repeat first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]
  simp only [EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem depositPublicInternalReverts {evm0 evm : State} {imms : Store}
    {assets shares cursor : UInt256} {receiver : AccountAddress}
    (hbody : ExecFuncBody config
      (erc4626DepositFrame imms evm.executionEnv.source receiver assets shares cursor) evm
      allocatedDepositFunction.body .reverted) :
    ExecBlock config
      (depositPublicCallerFrame (depositPublicSupplyFrame evm0 evm imms assets receiver cursor)
        shares evm.executionEnv.source) evm depositPublicFinish .reverted := by
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedDepositFunction)
    (depositPublicInternalArgs evm0 evm imms assets shares cursor receiver evm.executionEnv.source)
    rfl rfl hbody)

theorem depositPublicInternalReturns {evm0 evm evm' : State} {imms : Store}
    {assets shares cursor cursor' : UInt256} {receiver : AccountAddress} {final : Frame}
    (hbody : ExecFuncBody config
      (erc4626DepositFrame imms evm.executionEnv.source receiver assets shares cursor) evm
      allocatedDepositFunction.body (.returned final evm' (some [uint256Value cursor']))) :
    ExecBlock config
      (depositPublicCallerFrame (depositPublicSupplyFrame evm0 evm imms assets receiver cursor)
        shares evm.executionEnv.source) evm depositPublicFinish
      (.returned (resumeAfterInternalCall
        (depositPublicCallerFrame (depositPublicSupplyFrame evm0 evm imms assets receiver cursor)
          shares evm.executionEnv.source) "__c4" (some [uint256Value cursor']))
        evm' (some [uint256Value shares])) := by
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := allocatedDepositFunction)
    (depositPublicInternalArgs evm0 evm imms assets shares cursor receiver evm.executionEnv.source)
    rfl rfl hbody)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, depositPublicCallerFrame,
    depositPublicSharesFrame,
    store_get_ne _ _ (by decide : ("__c4" == "shares") = false),
    store_get_ne _ _ (by decide : ("__c3" == "shares") = false), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
