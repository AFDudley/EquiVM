import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultSource

/-! Metadata event source continuations keep the constructor frame and source state unchanged. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorVaultEmit (symbol : Bool) : Stmt :=
  .emit (if symbol then "SetSymbol" else "SetName") [.var (constructorVaultArgName symbol)]

theorem constructorVaultEmitBodySplit (symbol : Bool) :
    contract.ctor.body.drop (if symbol then 32 else 30) =
      constructorVaultEmit symbol :: contract.ctor.body.drop (if symbol then 33 else 31) := by
  cases symbol <;> rfl

theorem constructorVaultEmitSource {frame : Frame} {evm : State} {bytes : ByteArray} (symbol : Bool)
    (hget : frame.locals.get? (constructorVaultArgName symbol) = some (.bytes bytes)) :
    ExecStmt config frame evm (constructorVaultEmit symbol) (.ok frame evm) := by
  apply ExecStmt.emit (vals := [.bytes bytes])
  simp only [evalExprs?, evalExpr?, hget, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem constructorVaultEmitPrefix {frame : Frame} {evm : State} {bytes : ByteArray}
    {result : ExecResult} (symbol : Bool)
    (hget : frame.locals.get? (constructorVaultArgName symbol) = some (.bytes bytes))
    (hrest : ExecBlock config frame evm (contract.ctor.body.drop (if symbol then 33 else 31)) result) :
    ExecBlock config frame evm (contract.ctor.body.drop (if symbol then 32 else 30)) result := by
  rw [constructorVaultEmitBodySplit]
  exact ExecBlock.consNormal (constructorVaultEmitSource symbol hget) hrest

end Benchmarks.Morpho.MetaMorphoV1_1
