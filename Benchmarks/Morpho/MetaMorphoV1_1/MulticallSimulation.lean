import Benchmarks.Morpho.MetaMorphoV1_1.MulticallAllocationRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.MulticallLoop
import Benchmarks.Morpho.MetaMorphoV1_1.MulticallPrefixSource
import Benchmarks.Morpho.MetaMorphoV1_1.MulticallReturnRuntime

/-! Compose allocation, the delegatecall loop, and ABI return for the full multicall body. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem multicallSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out : ByteArray} {aw : UInt256} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 25 ≤ 1024)
    (hc : WordArrayCalldataChecks I.calldata) (hs : SourceState s0 I evm.accountMap evm)
    (hwv : I.weiValue = ⟨0⟩) (hmem : mem.size ≤ 96) (hfree : memLoad ⟨64⟩ mem = ⟨128⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨3814⟩
      (UInt256.ofNat (calldataArrayLength I.calldata) :: multicallInputBase I.calldata :: R)
      mem aw out evm.accountMap k C) :
    (ExecTransitionBody config contract evm ((∅ : Store).insert "data" (.array (multicallInput I.calldata)))
      allocatedMulticallTransition.body .reverted (immStore v) ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (frame : Frame) (evm' : State) (results : List ByteArray),
      ExecTransitionBody config contract evm ((∅ : Store).insert "data" (.array (multicallInput I.calldata)))
        allocatedMulticallTransition.body
        (.returned frame evm' (some [.array (results.map Value.bytes)])) (immStore v) ∧
      RDret (deployedRuntime v) g s0 evm'.accountMap (bytesArrayReturnBytes results) := by
  have hn : (multicallInput I.calldata).length ≤ solcMaxU64 := by
    rw [multicallInput_length hc]; exact hc.length
  have hp := multicallPrefixSource evm (immStore v) (multicallInput I.calldata)
    (by rw [hs.env]; exact hwv) (by rw [hs.env]; have := hc.size; omega) hn
  rcases multicallAllocate v (by omega) hc.length hfree rd with
    ⟨hbad, hrev⟩ | ⟨hfit, aw1, k1, C1, r1⟩
  · exact .inl ⟨ExecFuncBody.execBlockRevert (hp.run
      (multicallArrayRevertsSource evm (immStore v) (multicallInput I.calldata) hn
        (by rwa [multicallInput_length hc]))), hrev⟩
  have ha := multicallArrayPrefixSource evm (immStore v) (multicallInput I.calldata) hn
    (by rwa [multicallInput_length hc])
  have hr := multicallArrayFrame_ready evm (immStore v) (multicallInput I.calldata)
  rw [multicallInput_length hc] at hr
  have hm := multicallInitialMemory_ready mem (calldataArrayLength I.calldata) hmem hfit
  rcases multicallLoopSimulation v (calldataArrayLength I.calldata) hstack hc hs hr hm
      (List.length_replicate ..) (Nat.zero_add _).symm r1 with
    ⟨hbad, hrev⟩ | ⟨frame, mem', ptr', results, evm', out', aw2, k2, C2, hs', hr', hm', hlen, hloop, r2⟩
  · exact .inl ⟨ExecFuncBody.execBlockRevert (hp.run (ha.run
      (ExecBlock.consRevert (ExecStmt.for (multicallForInit _ _) hbad)))), hrev⟩
  · refine .inr ⟨frame, evm', results, ExecFuncBody.execBlockRet (hp.run (ha.run
      (ExecBlock.consNormal (ExecStmt.for (multicallForInit _ _) hloop) ?_))),
        multicallReturn v hstack hm' r2⟩
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, hr'.results, EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
