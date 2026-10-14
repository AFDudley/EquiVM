import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.MulticallABI
import Benchmarks.Morpho.MetaMorphoV1_1.MulticallEntry
import Benchmarks.Morpho.MetaMorphoV1_1.MulticallSimulation

/-!
# MetaMorphoV1_1 `multicall(bytes[])`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3766; reach lemma `metaMorphoV1_1ReachMulticallBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `multicall(bytes[])`: the theorem `Correct.lean` routes selector 50 to. -/
theorem metaMorphoV1_1MulticallBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 50)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 50) rfl hsel
  have hd : dispatchMsg contract I.calldata = some multicallTransition := by
    apply metaMorphoV1_1Dispatch_multicall <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachMulticallBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  case neg =>
    exact dispatchedRevert hcode hd (multicallNonpayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)
  have hdec := multicallDecode hsize hsel
  rcases multicallDecodeRuntime v (by simp) hwv hsz hsize rd with
    ⟨hc, hrev⟩ | ⟨hc, k1, C1, r1⟩
  · rw [if_neg hc] at hdec
    exact hrev.reEquivDecodingFailed hcode hd hdec
  · rw [if_pos hc] at hdec
    rcases multicallSimulation
        (R := [UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) (UInt256.ofNat 224)])
        (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) v (by simp) hc SourceState.init hwv
        (by rw [solcFreePtrMem_size]) solcFreePtrMem_mload64 r1 with
      ⟨hbody, hrev⟩ | ⟨frame, evm', results, hbody, hret⟩
    · exact hrev.reEquivExecutionRevert hcode hd hdec hbody
    · exact hret.reEquivExecutionGen hcode hd hdec hbody rfl
        (returnEquiv_of_encode (bytesArrayReturnEncoding results))

end Benchmarks.Morpho.MetaMorphoV1_1
