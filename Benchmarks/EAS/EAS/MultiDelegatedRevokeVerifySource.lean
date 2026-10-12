import Benchmarks.EAS.EAS.MultiDelegatedRevokeSource
import Benchmarks.EAS.EAS.MultiDelegatedRevokeVerifyPrepare
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure MultiDelegatedRevokeLocals (L : Store) (requests : List Value) (available : UInt256) (heap i : Nat) : Prop where
  requests : L.get? "multiDelegatedRequests" = some (.array requests)
  available : L.get? "availableValue" = some (.int (Int.ofNat available.toNat))
  heap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  index : L.get? "i" = some (.int (Int.ofNat i))

structure MultiDelegatedRevokeVerifyLocals (L : Store) (requests : List Value) (available : UInt256)
    (heap i j : Nat) (last : Bool) (r : DelegatedRevocationBatch) : Prop where
  outer : MultiDelegatedRevokeLocals L requests available heap i
  request : L.get? "multiDelegatedRequest" = some r.tuple
  data : L.get? "data" = some (.array (r.data.map RevocationRequestRecord.tuple))
  signatures : L.get? "signatures" = some (.array (r.signatures.map SignatureRecord.tuple))
  last : L.get? "last" = some (.bool last)
  index : L.get? "j" = some (.int (Int.ofNat j))

theorem MultiDelegatedRevokeLocals.allocated {L : Store} {requests : List Value} {available : UInt256} {heap i : Nat}
    (h : MultiDelegatedRevokeLocals L requests available heap i) (next : Nat) :
    MultiDelegatedRevokeLocals (allocateBlockLocals L next) requests available next i := by
  constructor <;> simp (disch := decide) only [allocateBlockLocals_get,allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self] <;>
    first | exact h.requests | exact h.available | exact h.index

theorem MultiDelegatedRevokeVerifyLocals.allocated {L : Store} {requests : List Value} {available : UInt256}
    {heap i j : Nat} {last : Bool} {r : DelegatedRevocationBatch}
    (h : MultiDelegatedRevokeVerifyLocals L requests available heap i j last r) (next : Nat) :
    MultiDelegatedRevokeVerifyLocals (allocateBlockLocals L next) requests available next i j last r := by
  refine ⟨h.outer.allocated next,?_,?_,?_,?_,?_⟩ <;>
    simp (disch := decide) only [allocateBlockLocals_get] <;>
    first | exact h.request | exact h.data | exact h.signatures | exact h.last | exact h.index

def multiDelegatedRevokeVerifyCallLocals (L : Store) (next : Nat) : Store :=
  heapResultLocals L "__c0$allocation" "__c0" "$EAS.freeMemory" (.tuple []) next

theorem MultiDelegatedRevokeVerifyLocals.called {L : Store} {requests : List Value} {available : UInt256}
    {heap i j : Nat} {last : Bool} {r : DelegatedRevocationBatch}
    (h : MultiDelegatedRevokeVerifyLocals L requests available heap i j last r) (next : Nat) :
    MultiDelegatedRevokeVerifyLocals (multiDelegatedRevokeVerifyCallLocals L next) requests available next i j last r := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · constructor <;> simp (disch := decide) only [multiDelegatedRevokeVerifyCallLocals,heapResultLocals_get,heapResultLocals_heap] <;>
      first | exact h.outer.requests | exact h.outer.available | exact h.outer.index
  all_goals simp (disch := decide) only [multiDelegatedRevokeVerifyCallLocals,heapResultLocals_get]
  all_goals first | exact h.request | exact h.data | exact h.signatures | exact h.last | exact h.index

theorem MultiDelegatedRevokeVerifyLocals.increment {L : Store} {requests : List Value} {available : UInt256}
    {heap i j : Nat} {last : Bool} {r : DelegatedRevocationBatch}
    (h : MultiDelegatedRevokeVerifyLocals L requests available heap i j last r) :
    MultiDelegatedRevokeVerifyLocals (L.insert "j" (.int (Int.ofNat (j+1)))) requests available heap i (j+1) last r := by
  refine ⟨?_,?_,?_,?_,?_,store_get_self _ _ _⟩
  · constructor <;> simp (disch := decide) only [store_get_ne] <;>
      first | exact h.outer.requests | exact h.outer.available | exact h.outer.heap | exact h.outer.index
  all_goals simp (disch := decide) only [store_get_ne]
  all_goals first | exact h.request | exact h.data | exact h.signatures | exact h.last

theorem multiDelegatedRevokeVerifyArgs_eval {L imms : Store} {evm : EVM.State} {requests : List Value}
    {available : UInt256} {heap i j : Nat} {last : Bool} {r : DelegatedRevocationBatch}
    (h : MultiDelegatedRevokeVerifyLocals L requests available heap i j last r)
    (hj : j < r.data.length) (hjs : j < r.signatures.length) :
    evalExprs? config {contract := contract,locals := L,immutables := imms} evm multiDelegatedRevokeVerifyArgs =
      .ok [(r.request j hj hjs).struct,.int (Int.ofNat heap)] := by
  have hd : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.index (.var "data") (.var "j")) = .ok r.data[j].tuple :=
    evalArrayIndex (evalLocalValue h.data) (evalLocalValue h.index) (by simpa only [List.length_map] using hj)
      (List.getElem_map ..) rfl
  have hs : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.index (.var "signatures") (.var "j")) = .ok r.signatures[j].tuple :=
    evalArrayIndex (evalLocalValue h.signatures) (evalLocalValue h.index) (by simpa only [List.length_map] using hjs)
      (List.getElem_map ..) rfl
  simp only [multiDelegatedRevokeVerifyArgs,evalExprs?,hd,hs,evalExpr?,evalStructFields?,h.request,h.outer.heap,
    DelegatedRevocationBatch.tuple,DelegatedRevocationBatch.request,DelegatedRevocationRecord.struct,
    EvalResult.ofOption,bind,EvalResult.bind,pure]
  rfl

end Benchmarks.EAS.EAS
