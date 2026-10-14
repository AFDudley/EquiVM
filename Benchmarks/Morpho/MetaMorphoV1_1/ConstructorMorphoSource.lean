import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultEventSource

/-! Source continuation through the symbol event and MORPHO assignment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] ConstructorArgs.encoded
set_option autoImplicit false

def constructorMorphoFrame (frame : Frame) (morpho : AccountAddress) : Frame :=
  { frame with immutables := frame.immutables.insert "MORPHO" (.address morpho) }

theorem constructorMorphoSource {frame : Frame} {evm : State} {morpho : AccountAddress}
    (hc : frame.contract = contract) (hm : frame.locals.get? "morpho" = some (.address morpho)) :
    ExecStmt config frame evm (.setImmutable "MORPHO" (.var "morpho"))
      (.ok (constructorMorphoFrame frame morpho) evm) := by
  exact ExecStmt.setImmutable (value := .address morpho) (ty := .address)
    (evalLocalValue hm) (by rw [hc]; rfl) rfl

theorem constructorMorphoPrefix (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) {evm : State} {result : ExecResult}
    (hrest : ExecBlock config
      (constructorMorphoFrame (constructorTimelockReadyFrame a ok out I) a.morpho) evm
      (contract.ctor.body.drop 34) result) :
    ExecBlock config (constructorTimelockReadyFrame a ok out I) evm
      (contract.ctor.body.drop 32) result := by
  apply constructorVaultEmitPrefix (frame := constructorTimelockReadyFrame a ok out I) true
    (constructorTimelockReadyFrame_string a ok out I true)
  change ExecBlock config _ evm
    (.setImmutable "MORPHO" (.var "morpho") :: contract.ctor.body.drop 34) result
  apply ExecBlock.consNormal (constructorMorphoSource
    (constructorTimelockReadyFrame_contract a ok out I) ?_) hrest
  rw [constructorTimelockReadyFrame_preserves a ok out I "morpho"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  change (constructorInputFrame a []).locals.get? "morpho" = _
  apply Std.HashMap.getElem?_ofList_of_mem (k := "morpho") (by decide) <;> simp

end Benchmarks.Morpho.MetaMorphoV1_1
