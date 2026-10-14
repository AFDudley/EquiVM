import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateEntry
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSimulation

/-!
# MetaMorphoV1_1 `reallocate(((address,address,address,address,uint256),uint256)[])`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 5836; reach lemma `metaMorphoV1_1ReachReallocateBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `reallocate(((address,address,address,address,uint256),uint256)[])`: the theorem `Correct.lean` routes selector 34 to. -/
theorem metaMorphoV1_1ReallocateBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 34)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 34) rfl hsel
  have hd : dispatchMsg contract I.calldata = some reallocateTransition := by
    apply metaMorphoV1_1Dispatch_reallocate <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachReallocateBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  case neg =>
    exact dispatchedRevert hcode hd (reallocateNonpayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)
  have hdec := reallocateDecodeChecks hsel hsize
  rcases reallocateDecodeRuntime v (by simp) hwv hsz hsize rd with
    ⟨hc, hrev⟩ | ⟨hc, k1, C1, r1⟩
  · rw [if_neg hc] at hdec
    exact hrev.reEquivDecodingFailed hcode hd hdec
  · rw [if_pos hc] at hdec
    rcases reallocateSimulation (R := [])
        (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) v (by simp) hc SourceState.init hwv
        (by rw [solcFreePtrMem_size]) solcFreePtrMem_mload64 r1 with
      ⟨hbody, hrev⟩ | ⟨hbody, hstatic⟩ | ⟨frame, evm', hbody, hret⟩
    · exact hrev.reEquivExecutionRevert hcode hd hdec hbody
    · exact hstatic.reEquivStaticHalt hcode hd hdec hbody
    · exact hret.reEquivExecutionGen hcode hd hdec hbody rfl voidReturnEquiv

end Benchmarks.Morpho.MetaMorphoV1_1
