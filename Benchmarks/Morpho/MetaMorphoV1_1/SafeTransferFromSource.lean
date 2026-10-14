import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferFromAllocationSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferFromABI
import Benchmarks.Morpho.MetaMorphoV1_1.EncodedOptionalCallSource

/-! Instantiate the shared encoded SafeERC20 wrapper for transferFrom. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def safeTransferFromFrame (imms : Store) (token sender recipient : AccountAddress)
    (amount ptr : UInt256) : Frame :=
  ⟨contract, (((((∅ : Store).insert cursorName (uint256Value ptr)).insert
    "value" (uint256Value amount)).insert "to" (.address recipient)).insert
    "from" (.address sender)).insert "token" (.address token), imms⟩

def safeTransferFromResultFrame (imms : Store) (token sender recipient : AccountAddress)
    (amount ptr cursor : UInt256) : Frame :=
  encodedOptionalResultFrame (safeTransferFromFrame imms token sender recipient amount ptr)
    (safeTransferFromCalldata sender recipient amount) ptr ⟨132⟩ cursor

theorem safeTransferFromEncodeSource (evm : State) (imms : Store)
    (token sender recipient : AccountAddress) (amount ptr : UInt256) :
    evalExpr? config (safeTransferFromFrame imms token sender recipient amount ptr) evm
      (.abiEncodeCall "transferFrom" [.var "from", .var "to", .var "value"]) =
      .ok (.bytes (safeTransferFromCalldata sender recipient amount)) := by
  simp [evalExpr?, evalExprList?, safeTransferFromFrame, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure, safeTransferFromEncode]

theorem safeTransferFromFrame_cursor (imms : Store) (token sender recipient : AccountAddress)
    (amount ptr : UInt256) :
    (safeTransferFromFrame imms token sender recipient amount ptr).locals.get? cursorName =
      some (uint256Value ptr) := by
  simp [safeTransferFromFrame, cursorName, Std.HashMap.getElem_insert]

theorem safeTransferFromBodyReturns {evm evm' : State} (imms : Store)
    (token sender recipient : AccountAddress) (amount ptr cursor : UInt256) {frame' : Frame}
    (hf : allocationFits ptr ⟨132⟩)
    (hcall : ExecFuncBody config
      (optionalCallFrame imms token (safeTransferFromCalldata sender recipient amount) (nextCursor ptr ⟨132⟩))
      evm allocatedOptionalReturnFunction.body (.returned frame' evm' (some [uint256Value cursor]))) :
    ExecFuncBody config (safeTransferFromFrame imms token sender recipient amount ptr) evm
      allocatedSafeTransferFromFunction.body
      (.returned (safeTransferFromResultFrame imms token sender recipient amount ptr cursor) evm'
        (some [uint256Value cursor])) :=
  encodedOptionalReturns rfl (safeTransferFromEncodeSource evm imms token sender recipient amount ptr)
    (safeTransferFromFrame_cursor imms token sender recipient amount ptr) (store_get_self _ _ _) hf hcall

theorem safeTransferFromBodyRevertsCall (evm : State) (imms : Store)
    (token sender recipient : AccountAddress) (amount ptr : UInt256) (hf : allocationFits ptr ⟨132⟩)
    (hcall : ExecFuncBody config
      (optionalCallFrame imms token (safeTransferFromCalldata sender recipient amount) (nextCursor ptr ⟨132⟩))
      evm allocatedOptionalReturnFunction.body .reverted) :
    ExecFuncBody config (safeTransferFromFrame imms token sender recipient amount ptr) evm
      allocatedSafeTransferFromFunction.body .reverted :=
  encodedOptionalRevertsCall rfl (safeTransferFromEncodeSource evm imms token sender recipient amount ptr)
    (safeTransferFromFrame_cursor imms token sender recipient amount ptr) (store_get_self _ _ _) hf hcall

theorem safeTransferFromBodyRevertsAllocation (evm : State) (imms : Store)
    (token sender recipient : AccountAddress) (amount ptr : UInt256) (hf : ¬ allocationFits ptr ⟨132⟩) :
    ExecFuncBody config (safeTransferFromFrame imms token sender recipient amount ptr) evm
      allocatedSafeTransferFromFunction.body .reverted :=
  encodedOptionalRevertsAllocation rfl (safeTransferFromEncodeSource evm imms token sender recipient amount ptr)
    (safeTransferFromFrame_cursor imms token sender recipient amount ptr) hf

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
