import Benchmarks.Morpho.MetaMorphoV1_1.DepositInternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedFeeSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertAssetsUpSource
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalCalls

/-! Public mint source composition using upward asset conversion and the shared deposit. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def mintPublicLocals (shares : UInt256) (receiver : AccountAddress) : Store :=
  ((∅ : Store).insert "shares" (uint256Value shares)).insert "receiver" (.address receiver)

def mintPublicFrame (evm : State) (imms : Store) (shares : UInt256)
    (receiver : AccountAddress) : Frame :=
  ⟨contract, (((mintPublicLocals shares receiver).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).insert cursorName (uint256Value ⟨128⟩)).insert
      "assets" (uint256Value ⟨0⟩), imms⟩

def mintPublicAccruedFrame (evm : State) (imms : Store) (shares : UInt256)
    (receiver : AccountAddress) (cursor : UInt256) : Frame :=
  let f := mintPublicFrame evm imms shares receiver
  { f with locals := f.locals.insert cursorName (uint256Value cursor) }

def mintPublicSupplyFrame (evm evm' : State) (imms : Store) (shares : UInt256)
    (receiver : AccountAddress) (cursor : UInt256) : Frame :=
  let f := mintPublicAccruedFrame evm imms shares receiver cursor
  { f with locals := f.locals.insert "__c1" (uint256Value
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)) }

def mintPublicReadyFrame (frame : Frame) (assets : UInt256) (caller : AccountAddress) : Frame :=
  { frame with locals := ((frame.locals.insert "__c2" (uint256Value assets)).insert
      "assets" (uint256Value assets)).insert "__c3" (.address caller) }

def mintPublicFinish : List Stmt :=
  [.internalCall allocatedDepositFunction.name
    [.var "__c3", .var "receiver", .var "assets", .var "shares", .var cursorName] "__c4",
   .return [.var "assets"]]

def mintPublicConversion : List Stmt :=
  [.internalCall "totalSupply_body" [] "__c1",
   .internalCall "_convertToAssetsWithTotals"
     [.var "shares", .var "__c1", .storage ⟨"lastTotalAssets", []⟩, .intLit 1] "__c2",
   .assign .localVar ⟨"assets", []⟩ (.var "__c2"),
   .internalCall "_msgSender" [] "__c3"] ++ mintPublicFinish

def mintPublicAccrual : List Stmt :=
  .internalCall allocatedAccrueInterestFunction.name [.var cursorName] cursorName ::
    mintPublicConversion

theorem mintPublicPrefix (evm : State) (imms : Store) (shares : UInt256)
    (receiver : AccountAddress) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, mintPublicLocals shares receiver, imms⟩
      mintTransition.body (mintPublicFrame evm imms shares receiver) mintPublicAccrual := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨128⟩)
    (by simp only [evalExpr?, pure]; rfl))
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl)) htail

theorem mintPublicAccrualArgs (evm : State) (imms : Store) (shares : UInt256)
    (receiver : AccountAddress) :
    evalExprs? config (mintPublicFrame evm imms shares receiver) evm [.var cursorName] =
      .ok [uint256Value ⟨128⟩] := by
  simp only [evalExprs?, evalExpr?, mintPublicFrame,
    store_get_ne _ _ (by decide : ("assets" == cursorName) = false), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem mintPublicAccrualReverts {evm : State} {imms : Store} {shares : UInt256}
    {receiver : AccountAddress}
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body .reverted) :
    ExecBlock config (mintPublicFrame evm imms shares receiver) evm mintPublicAccrual .reverted := by
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (callee := allocatedAccrueInterestFunction)
    (mintPublicAccrualArgs evm imms shares receiver) rfl rfl hbody)

theorem mintPublicAccrualStatic {evm : State} {imms : Store} {shares : UInt256}
    {receiver : AccountAddress}
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body .staticViolation) :
    ExecBlock config (mintPublicFrame evm imms shares receiver) evm
      mintPublicAccrual .staticViolation := by
  exact ExecBlock.consStatic (ExecStmt.internalCallStatic
    (callee := allocatedAccrueInterestFunction.toCallable)
    (mintPublicAccrualArgs evm imms shares receiver) rfl rfl hbody)

theorem mintPublicAccrualContinue {evm evm' : State} {imms : Store} {shares cursor : UInt256}
    {receiver : AccountAddress} {final : Frame} {result : ExecResult}
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body (.returned final evm' (some [uint256Value cursor])))
    (htail : ExecBlock config (mintPublicAccruedFrame evm imms shares receiver cursor) evm'
      mintPublicConversion result) :
    ExecBlock config (mintPublicFrame evm imms shares receiver) evm mintPublicAccrual result := by
  exact ExecBlock.consNormal (internalCallFunctionReturn
    (callee := allocatedAccrueInterestFunction)
    (mintPublicAccrualArgs evm imms shares receiver) rfl rfl hbody) htail

theorem mintPublicConversionArgs (evm evm' : State) (imms : Store) (shares : UInt256)
    (receiver : AccountAddress) (cursor : UInt256) :
    evalExprs? config (mintPublicSupplyFrame evm evm' imms shares receiver cursor) evm'
      [.var "shares", .var "__c1", .storage ⟨"lastTotalAssets", []⟩, .intLit 1] =
      .ok [uint256Value shares,
        uint256Value (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩),
        uint256Value (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩),
        uint256Value ⟨1⟩] := by
  have hn : (mintPublicSupplyFrame evm evm' imms shares receiver cursor).locals.get?
      "lastTotalAssets" = none := by
    simp [mintPublicSupplyFrame, mintPublicAccruedFrame, mintPublicFrame, mintPublicLocals, cursorName]
  have ht := depositLastAssetsSource (frame :=
    mintPublicSupplyFrame evm evm' imms shares receiver cursor) (evm := evm') rfl hn
  simp only [evalExprs?, ht]
  simp only [evalExpr?, mintPublicSupplyFrame, mintPublicAccruedFrame,
    mintPublicFrame, mintPublicLocals, store_get_self]
  repeat rw [store_get_ne _ _ (by decide)]
  simp only [store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

theorem mintPublicConversionReverts (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} {shares cursor : UInt256} {receiver : AccountAddress}
    (hbad : ¬ convertAssetsUpFits v.DECIMALS_OFFSET shares
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩)) :
    ExecBlock config (mintPublicAccruedFrame evm (immStore v) shares receiver cursor) evm'
      mintPublicConversion .reverted := by
  exact ExecBlock.consNormal (totalSupplyInternalCall _ _ _ "__c1")
    (ExecBlock.consRevert (convertAssetsUpCallReverts v
      (mintPublicConversionArgs evm evm' (immStore v) shares receiver cursor) hbad))

theorem mintPublicConversionPrefix (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} {shares cursor : UInt256} {receiver : AccountAddress}
    (hfit : convertAssetsUpFits v.DECIMALS_OFFSET shares
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)
      (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩)) :
    ABlock config evm' (mintPublicAccruedFrame evm (immStore v) shares receiver cursor)
      mintPublicConversion
      (mintPublicReadyFrame (mintPublicSupplyFrame evm evm' (immStore v) shares receiver cursor)
        (convertAssetsUpWord v.DECIMALS_OFFSET shares
          (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩)
          (Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨22⟩)) evm'.executionEnv.source)
      mintPublicFinish := by
  constructor
  intro result htail
  apply ExecBlock.consNormal (totalSupplyInternalCall _ _ _ "__c1")
  apply ExecBlock.consNormal (convertAssetsUpCall v
    (mintPublicConversionArgs evm evm' (immStore v) shares receiver cursor) hfit)
  apply ExecBlock.consNormal (ExecStmt.assign (evalLocalValue (store_get_self ..))
    (assignLocalValue (old := uint256Value ⟨0⟩) ?_))
  · exact ExecBlock.consNormal (msgSenderCall _ _ _ "__c3") htail
  · simp only [mintPublicSupplyFrame, mintPublicAccruedFrame, mintPublicFrame]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self ..

theorem mintPublicInternalArgs (evm0 evm : State) (imms : Store) (assets shares cursor : UInt256)
    (receiver caller : AccountAddress) :
    evalExprs? config
      (mintPublicReadyFrame (mintPublicSupplyFrame evm0 evm imms shares receiver cursor)
        assets caller) evm
      [.var "__c3", .var "receiver", .var "assets", .var "shares", .var cursorName] =
      .ok [.address caller, .address receiver, uint256Value assets, uint256Value shares,
        uint256Value cursor] := by
  simp only [evalExprs?, evalExpr?, mintPublicReadyFrame, mintPublicSupplyFrame, mintPublicAccruedFrame,
    mintPublicFrame, mintPublicLocals]
  repeat first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]
  simp only [EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem mintPublicInternalReverts {evm0 evm : State} {imms : Store}
    {assets shares cursor : UInt256} {receiver : AccountAddress}
    (hbody : ExecFuncBody config
      (erc4626DepositFrame imms evm.executionEnv.source receiver assets shares cursor) evm
      allocatedDepositFunction.body .reverted) :
    ExecBlock config
      (mintPublicReadyFrame (mintPublicSupplyFrame evm0 evm imms shares receiver cursor)
        assets evm.executionEnv.source) evm mintPublicFinish .reverted := by
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedDepositFunction)
    (mintPublicInternalArgs evm0 evm imms assets shares cursor receiver evm.executionEnv.source)
    rfl rfl hbody)

theorem mintPublicInternalReturns {evm0 evm evm' : State} {imms : Store}
    {assets shares cursor cursor' : UInt256} {receiver : AccountAddress} {final : Frame}
    (hbody : ExecFuncBody config
      (erc4626DepositFrame imms evm.executionEnv.source receiver assets shares cursor) evm
      allocatedDepositFunction.body (.returned final evm' (some [uint256Value cursor']))) :
    ExecBlock config
      (mintPublicReadyFrame (mintPublicSupplyFrame evm0 evm imms shares receiver cursor)
        assets evm.executionEnv.source) evm mintPublicFinish
      (.returned (resumeAfterInternalCall
        (mintPublicReadyFrame (mintPublicSupplyFrame evm0 evm imms shares receiver cursor)
          assets evm.executionEnv.source) "__c4" (some [uint256Value cursor']))
        evm' (some [uint256Value assets])) := by
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := allocatedDepositFunction)
    (mintPublicInternalArgs evm0 evm imms assets shares cursor receiver evm.executionEnv.source)
    rfl rfl hbody)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, mintPublicReadyFrame,
    store_get_ne _ _ (by decide : ("__c4" == "assets") = false),
    store_get_ne _ _ (by decide : ("__c3" == "assets") = false), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
