import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawInternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.DepositFinishSource
import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedFeeSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertAssetsSource
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalCalls

/-! Public redemption source composition with downward asset conversion. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def redeemPublicLocals (shares : UInt256) (receiver owner : AccountAddress) : Store :=
  (((∅ : Store).insert "shares" (uint256Value shares)).insert "receiver" (.address receiver)).insert
    "owner" (.address owner)

def redeemPublicFrame (evm : State) (imms : Store) (shares : UInt256)
    (receiver owner : AccountAddress) : Frame :=
  ⟨contract, (((redeemPublicLocals shares receiver owner).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).insert cursorName (uint256Value ⟨128⟩)).insert
      "assets" (uint256Value ⟨0⟩), imms⟩

def redeemPublicAccruedFrame (evm : State) (imms : Store) (shares : UInt256)
    (receiver owner : AccountAddress) (cursor : UInt256) : Frame :=
  let f := redeemPublicFrame evm imms shares receiver owner
  { f with locals := f.locals.insert cursorName (uint256Value cursor) }

def redeemPublicSupplyFrame (evm evm' : State) (imms : Store) (shares : UInt256)
    (receiver owner : AccountAddress) (cursor : UInt256) : Frame :=
  let f := redeemPublicAccruedFrame evm imms shares receiver owner cursor
  { f with locals := f.locals.insert "__c1" (uint256Value
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)) }

def redeemPublicReadyFrame (frame : Frame) (assets : UInt256) (caller : AccountAddress) : Frame :=
  { frame with locals := ((frame.locals.insert "__c2" (uint256Value assets)).insert
      "assets" (uint256Value assets)).insert "__c3" (.address caller) }

def redeemPublicFinish : List Stmt :=
  [.internalCall allocatedWithdrawFunction.name
    [.var "__c3", .var "receiver", .var "owner", .var "assets", .var "shares", .var cursorName] "__c4",
   .return [.var "assets"]]

def redeemPublicConversion : List Stmt :=
  [.internalCall "totalSupply_body" [] "__c1",
   .internalCall "_convertToAssetsWithTotals"
     [.var "shares", .var "__c1", .storage ⟨"lastTotalAssets", []⟩, .intLit 0] "__c2",
   .assign .localVar ⟨"assets", []⟩ (.var "__c2"),
   .internalCall "_msgSender" [] "__c3"] ++ redeemPublicFinish

def redeemPublicAccrual : List Stmt :=
  .internalCall allocatedAccrueInterestFunction.name [.var cursorName] cursorName ::
    redeemPublicConversion

theorem redeemPublicPrefix (evm : State) (imms : Store) (shares : UInt256)
    (receiver owner : AccountAddress) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, redeemPublicLocals shares receiver owner, imms⟩
      redeemTransition.body (redeemPublicFrame evm imms shares receiver owner) redeemPublicAccrual := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨128⟩)
    (by simp only [evalExpr?, pure]; rfl))
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl)) htail

theorem redeemPublicAccrualArgs (evm : State) (imms : Store) (shares : UInt256)
    (receiver owner : AccountAddress) :
    evalExprs? config (redeemPublicFrame evm imms shares receiver owner) evm [.var cursorName] =
      .ok [uint256Value ⟨128⟩] := by
  simp only [evalExprs?, evalExpr?, redeemPublicFrame,
    store_get_ne _ _ (by decide : ("assets" == cursorName) = false), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem redeemPublicAccrualReverts {evm : State} {imms : Store} {shares : UInt256}
    {receiver owner : AccountAddress}
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body .reverted) :
    ExecBlock config (redeemPublicFrame evm imms shares receiver owner) evm redeemPublicAccrual .reverted := by
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (callee := allocatedAccrueInterestFunction)
    (redeemPublicAccrualArgs evm imms shares receiver owner) rfl rfl hbody)

theorem redeemPublicAccrualStatic {evm : State} {imms : Store} {shares : UInt256}
    {receiver owner : AccountAddress}
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body .staticViolation) :
    ExecBlock config (redeemPublicFrame evm imms shares receiver owner) evm
      redeemPublicAccrual .staticViolation := by
  exact ExecBlock.consStatic (ExecStmt.internalCallStatic
    (callee := allocatedAccrueInterestFunction.toCallable)
    (redeemPublicAccrualArgs evm imms shares receiver owner) rfl rfl hbody)

theorem redeemPublicAccrualContinue {evm evm' : State} {imms : Store} {shares cursor : UInt256}
    {receiver owner : AccountAddress} {final : Frame} {result : ExecResult}
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body (.returned final evm' (some [uint256Value cursor])))
    (htail : ExecBlock config (redeemPublicAccruedFrame evm imms shares receiver owner cursor) evm'
      redeemPublicConversion result) :
    ExecBlock config (redeemPublicFrame evm imms shares receiver owner) evm redeemPublicAccrual result := by
  exact ExecBlock.consNormal (internalCallFunctionReturn
    (callee := allocatedAccrueInterestFunction)
    (redeemPublicAccrualArgs evm imms shares receiver owner) rfl rfl hbody) htail

theorem redeemPublicConversionArgs (evm evm' : State) (imms : Store) (shares : UInt256)
    (receiver owner : AccountAddress) (cursor : UInt256) :
    evalExprs? config (redeemPublicSupplyFrame evm evm' imms shares receiver owner cursor) evm'
      [.var "shares", .var "__c1", .storage ⟨"lastTotalAssets", []⟩, .intLit 0] =
      .ok [uint256Value shares,
        uint256Value (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩),
        uint256Value (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩),
        uint256Value ⟨0⟩] := by
  have hn : (redeemPublicSupplyFrame evm evm' imms shares receiver owner cursor).locals.get?
      "lastTotalAssets" = none := by
    simp [redeemPublicSupplyFrame, redeemPublicAccruedFrame, redeemPublicFrame, redeemPublicLocals, cursorName]
  have ht := depositLastAssetsSource (frame :=
    redeemPublicSupplyFrame evm evm' imms shares receiver owner cursor) (evm := evm') rfl hn
  simp only [evalExprs?, ht]
  simp only [evalExpr?, redeemPublicSupplyFrame, redeemPublicAccruedFrame,
    redeemPublicFrame, redeemPublicLocals, store_get_self]
  repeat rw [store_get_ne _ _ (by decide)]
  simp only [store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

theorem redeemPublicConversionReverts (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} {shares cursor : UInt256} {receiver owner : AccountAddress}
    (hbad : ¬ convertAssetsFits v.DECIMALS_OFFSET shares
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩)) :
    ExecBlock config (redeemPublicAccruedFrame evm (immStore v) shares receiver owner cursor) evm'
      redeemPublicConversion .reverted := by
  exact ExecBlock.consNormal (totalSupplyInternalCall _ _ _ "__c1")
    (ExecBlock.consRevert (convertAssetsCallReverts v
      (redeemPublicConversionArgs evm evm' (immStore v) shares receiver owner cursor) hbad))

theorem redeemPublicConversionPrefix (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} {shares cursor : UInt256} {receiver owner : AccountAddress}
    (hfit : convertAssetsFits v.DECIMALS_OFFSET shares
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩)) :
    ABlock config evm' (redeemPublicAccruedFrame evm (immStore v) shares receiver owner cursor)
      redeemPublicConversion
      (redeemPublicReadyFrame (redeemPublicSupplyFrame evm evm' (immStore v) shares receiver owner cursor)
        (convertAssetsWord v.DECIMALS_OFFSET shares
          (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)
          (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩)) evm'.executionEnv.source)
      redeemPublicFinish := by
  constructor
  intro result htail
  apply ExecBlock.consNormal (totalSupplyInternalCall _ _ _ "__c1")
  apply ExecBlock.consNormal (convertAssetsCall v
    (redeemPublicConversionArgs evm evm' (immStore v) shares receiver owner cursor) hfit)
  apply ExecBlock.consNormal (ExecStmt.assign (evalLocalValue (store_get_self ..))
    (assignLocalValue (old := uint256Value ⟨0⟩) ?_))
  · exact ExecBlock.consNormal (msgSenderCall _ _ _ "__c3") htail
  · simp only [redeemPublicSupplyFrame, redeemPublicAccruedFrame, redeemPublicFrame]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self ..

theorem redeemPublicInternalArgs (evm0 evm : State) (imms : Store) (assets shares cursor : UInt256)
    (receiver owner caller : AccountAddress) :
    evalExprs? config
      (redeemPublicReadyFrame (redeemPublicSupplyFrame evm0 evm imms shares receiver owner cursor)
        assets caller) evm
      [.var "__c3", .var "receiver", .var "owner", .var "assets", .var "shares", .var cursorName] =
      .ok [.address caller, .address receiver, .address owner, uint256Value assets, uint256Value shares,
        uint256Value cursor] := by
  simp only [evalExprs?, evalExpr?, redeemPublicReadyFrame, redeemPublicSupplyFrame, redeemPublicAccruedFrame,
    redeemPublicFrame, redeemPublicLocals]
  repeat first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]
  simp only [EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem redeemPublicInternalReverts {evm0 evm : State} {imms : Store}
    {assets shares cursor : UInt256} {receiver owner : AccountAddress}
    (hbody : ExecFuncBody config
      (erc4626WithdrawFrame imms evm.executionEnv.source receiver owner assets shares cursor) evm
      allocatedWithdrawFunction.body .reverted) :
    ExecBlock config
      (redeemPublicReadyFrame (redeemPublicSupplyFrame evm0 evm imms shares receiver owner cursor)
        assets evm.executionEnv.source) evm redeemPublicFinish .reverted := by
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedWithdrawFunction)
    (redeemPublicInternalArgs evm0 evm imms assets shares cursor receiver owner evm.executionEnv.source)
    rfl rfl hbody)

theorem redeemPublicInternalReturns {evm0 evm evm' : State} {imms : Store}
    {assets shares cursor cursor' : UInt256} {receiver owner : AccountAddress} {final : Frame}
    (hbody : ExecFuncBody config
      (erc4626WithdrawFrame imms evm.executionEnv.source receiver owner assets shares cursor) evm
      allocatedWithdrawFunction.body (.returned final evm' (some [uint256Value cursor']))) :
    ExecBlock config
      (redeemPublicReadyFrame (redeemPublicSupplyFrame evm0 evm imms shares receiver owner cursor)
        assets evm.executionEnv.source) evm redeemPublicFinish
      (.returned (resumeAfterInternalCall
        (redeemPublicReadyFrame (redeemPublicSupplyFrame evm0 evm imms shares receiver owner cursor)
          assets evm.executionEnv.source) "__c4" (some [uint256Value cursor']))
        evm' (some [uint256Value assets])) := by
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := allocatedWithdrawFunction)
    (redeemPublicInternalArgs evm0 evm imms assets shares cursor receiver owner evm.executionEnv.source)
    rfl rfl hbody)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, redeemPublicReadyFrame,
    store_get_ne _ _ (by decide : ("__c4" == "assets") = false),
    store_get_ne _ _ (by decide : ("__c3" == "assets") = false), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
