import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDeployedCode
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorImmutableMemory

/-! Package a successful source constructor and the immutable-patched runtime return. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

-- LIBRARY CANDIDATE: constructor success packaging for arbitrary parameters and final accounts.
theorem constructorRefinementOfSuccess {cfg : Config} {decl : ContractDecl}
    {args : List Value} {runtimeCodeOf : Store → ByteArray} {frame : Frame} {evm : State}
    {code : ByteArray} {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = code)
    (hevm : RDret code (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      evm.accountMap (runtimeCodeOf frame.immutables))
    (hsource : steleCtorExec cfg decl args σ σ₀ g A I (.returned frame evm none))
    (hfit : immutablesFit decl frame.immutables) :
    typedConstructorRefinementFor cfg decl args σ σ₀ g A I runtimeCodeOf := by
  obtain hoog | ⟨s, hX, hacc⟩ := hevm
  · exact .outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hoog; exact hoog))
  · have hxi := Xi_success_of_X (g := g) (by rw [← hcode] at hX; exact hX)
    rw [hacc] at hxi
    exact .execution hxi hsource (.success rfl rfl rfl rfl) hfit

theorem constructorSourceSuccessOfPrefix {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : UInt256} {frame final : Frame} {rest : List Stmt} {evm : State}
    (a : ConstructorArgs)
    (hprefix : ABlock config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (constructorFrame a) contract.ctor.body frame rest)
    (hrest : ExecBlock config frame (initState σ σ₀ (Sat256.ofUInt256 g) A I) rest (.ok final evm)) :
    steleCtorExec config contract a.values σ σ₀ g A I (.returned final evm none) :=
  .intro rfl a.values_length (constructorLocals_bind a) (.execBlockOK (hprefix.run hrest))

end Benchmarks.Morpho.MetaMorphoV1_1
