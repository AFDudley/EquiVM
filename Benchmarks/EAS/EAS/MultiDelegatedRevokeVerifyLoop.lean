import Benchmarks.EAS.EAS.MultiDelegatedRevokeVerifyIteration
import Benchmarks.EAS.EAS.WhileInvariant
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedRevokeVerifyLoop : Stmt := .while (localArrayGuard "j" "data") multiDelegatedRevokeVerifyIteration

theorem multiDelegatedRevokeVerifyLoopRun {L : Store} {evm : EVM.State}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {requests : List Value} {r : DelegatedRevocationBatch}
    {n i : Nat} {base available row data sig : UInt256} {initial : ByteArray} {start : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+32 ≤ 1024) (hlen : r.data.length=r.signatures.length)
    (h : MultiDelegatedRevokeVerifyAt v ee g s0 requests r n i base available row data sig initial start R 0 L evm) :
    (∃ L' evm', ExecStmt config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeVerifyLoop
      (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      MultiDelegatedRevokeVerifyAt v ee g s0 requests r n i base available row data sig initial start R r.data.length L' evm') ∨
    (ExecStmt config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeVerifyLoop .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecStmt config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeVerifyLoop .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) := by
  apply execWhile_invariant
    (MultiDelegatedRevokeVerifyAt v ee g s0 requests r n i base available row data sig initial start R)
    (MultiDelegatedRevokeVerifyAt v ee g s0 requests r n i base available row data sig initial start R r.data.length)
    (RDrev (deployedRuntime v) g s0) (RDstatic (deployedRuntime v) g s0)
    ?_ (fun _ _ h => h) ?_ r.data.length 0 L evm (by omega) h
  · rintro j L1 e1 _ ⟨σ,mem,out,aw,k,C,heap,_,_,_,_,hf,_,_,_⟩
    simpa only [List.length_map] using evalLocalArrayGuard (cfg := config)
      (frame := {contract := contract,locals := L1,immutables := immStore v}) (evm := e1) hf.index hf.data
  · intro j L1 e1 hj h1
    exact multiDelegatedRevokeVerifyIterationRun v hstack hlen hj h1

end Benchmarks.EAS.EAS
