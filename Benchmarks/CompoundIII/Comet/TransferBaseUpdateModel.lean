import Benchmarks.CompoundIII.Comet.UpdateBaseModel

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def transferBaseUpdateOutcome (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (src dst : AccountAddress) (srcBasic dstBasic : UserBasicData) (srcNext dstNext : UInt256) :
    InternalOutcome :=
  match updateBaseOutcome v evm src srcBasic srcNext with
  | .ok evm' => updateBaseOutcome v evm' dst dstBasic dstNext
  | .reverted => .reverted
  | .staticViolation => .staticViolation

def transferBaseUpdateBlock : List Stmt :=
  [.internalCall "updateBasePrincipal" [.var "src", .var "srcUser", .var "srcPrincipalNew"] "__c9",
    .internalCall "updateBasePrincipal" [.var "dst", .var "dstUser", .var "dstPrincipalNew"] "__c10"]

def transferBaseUpdatedFrame (frame : Frame) : Frame :=
  { frame with locals := (frame.locals.insert "__c9" .unit).insert "__c10" .unit }

def transferBaseUpdateResult (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (src dst : AccountAddress) (srcBasic dstBasic : UserBasicData)
    (srcNext dstNext : UInt256) : ExecResult :=
  match transferBaseUpdateOutcome v evm src dst srcBasic dstBasic srcNext dstNext with
  | .ok evm' => .ok (transferBaseUpdatedFrame frame) evm'
  | .reverted => .reverted
  | .staticViolation => .staticViolation

theorem transferBaseUpdateOutcome_result_perm
    {v evm src dst srcBasic dstBasic srcNext dstNext updated}
    (hu : transferBaseUpdateOutcome v evm src dst srcBasic dstBasic srcNext dstNext = .ok updated) :
    updated.executionEnv.perm = true := by
  unfold transferBaseUpdateOutcome at hu
  split at hu
  · exact updateBaseOutcome_result_perm hu
  · cases hu
  · cases hu

end Benchmarks.CompoundIII.Comet
