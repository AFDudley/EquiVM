import Benchmarks.EAS.EAS.MultiDelegatedAttestDatumAllocate
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure MultiDelegatedAttestLocals (L : Store) (requests : List Value) (uidLists : List (List UInt256))
    (available : UInt256) (heap i : Nat) : Prop where
  requests : L.get? "multiDelegatedRequests"=some (.array requests)
  groups : L.get? "totalUids"=some (.array (uidLists.map wordListValue))
  count : L.get? "totalUidsCount"=some (.int (Int.ofNat uidLists.flatten.length))
  available : L.get? "availableValue"=some (.int (Int.ofNat available.toNat))
  heap : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap))
  index : L.get? "i"=some (.int (Int.ofNat i))

structure MultiDelegatedAttestVerifyLocals (L : Store) (requests : List Value) (groups : List (List UInt256))
    (available : UInt256) (heap i j : Nat) (last : Bool) (row : Value) (data sigs : List Value) : Prop where
  outer : MultiDelegatedAttestLocals L requests groups available heap i
  request : L.get? "multiDelegatedRequest"=some row
  data : L.get? "data"=some (.array data)
  signatures : L.get? "signatures"=some (.array sigs)
  last : L.get? "last"=some (.bool last)
  index : L.get? "j"=some (.int (Int.ofNat j))

theorem MultiDelegatedAttestVerifyLocals.datumRead {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i j : Nat} {last : Bool} {row : Value} {data sigs : List Value}
    (h : MultiDelegatedAttestVerifyLocals L requests groups available heap i j last row data sigs) (datum signature attester : Value) :
    MultiDelegatedAttestVerifyLocals (multiDelegatedAttestDatumLocals L datum signature attester) requests groups available heap i j last row data sigs := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · constructor <;> simp (disch := decide) only [multiDelegatedAttestDatumLocals,store_get_ne] <;>
      first | exact h.outer.requests | exact h.outer.groups | exact h.outer.count | exact h.outer.available | exact h.outer.heap | exact h.outer.index
  all_goals simp (disch := decide) only [multiDelegatedAttestDatumLocals,store_get_ne]
  all_goals first | exact h.request | exact h.data | exact h.signatures | exact h.last | exact h.index

theorem MultiDelegatedAttestVerifyLocals.allocated {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i j : Nat} {last : Bool} {row : Value} {data sigs : List Value}
    (h : MultiDelegatedAttestVerifyLocals L requests groups available heap i j last row data sigs) (next : Nat) :
    MultiDelegatedAttestVerifyLocals (allocateBlockLocals L next) requests groups available next i j last row data sigs := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · constructor <;> simp (disch := decide) only [allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self] <;>
      first | exact h.outer.requests | exact h.outer.groups | exact h.outer.count | exact h.outer.available | exact h.outer.heap | exact h.outer.index
  all_goals simp (disch := decide) only [allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
  all_goals first | exact h.request | exact h.data | exact h.signatures | exact h.last | exact h.index

theorem MultiDelegatedAttestVerifyLocals.copied {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i j : Nat} {last : Bool} {row : Value} {data sigs : List Value}
    (h : MultiDelegatedAttestVerifyLocals L requests groups available heap i j last row data sigs) (next : Nat) :
    MultiDelegatedAttestVerifyLocals (multiAttestCopyLocals L next) requests groups available next i j last row data sigs := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · constructor <;> simp (disch := decide) only [multiAttestCopyLocals,heapResultLocals_get,heapResultLocals_heap] <;>
      first | exact h.outer.requests | exact h.outer.groups | exact h.outer.count | exact h.outer.available | exact h.outer.heap | exact h.outer.index
  all_goals simp (disch := decide) only [multiAttestCopyLocals,heapResultLocals_get,heapResultLocals_heap]
  all_goals first | exact h.request | exact h.data | exact h.signatures | exact h.last | exact h.index

theorem MultiDelegatedAttestVerifyLocals.called {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i j : Nat} {last : Bool} {row : Value} {data sigs : List Value}
    (h : MultiDelegatedAttestVerifyLocals L requests groups available heap i j last row data sigs) (next : Nat) :
    MultiDelegatedAttestVerifyLocals (heapResultLocals L "__c0$allocation" "__c0" "$EAS.freeMemory" (.tuple []) next) requests groups available next i j last row data sigs := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · constructor <;> simp (disch := decide) only [heapResultLocals_get,heapResultLocals_heap] <;>
      first | exact h.outer.requests | exact h.outer.groups | exact h.outer.count | exact h.outer.available | exact h.outer.heap | exact h.outer.index
  all_goals simp (disch := decide) only [heapResultLocals_get,heapResultLocals_heap]
  all_goals first | exact h.request | exact h.data | exact h.signatures | exact h.last | exact h.index

theorem MultiDelegatedAttestVerifyLocals.increment {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i j : Nat} {last : Bool} {row : Value} {data sigs : List Value}
    (h : MultiDelegatedAttestVerifyLocals L requests groups available heap i j last row data sigs)  :
    MultiDelegatedAttestVerifyLocals (L.insert "j" (.int (Int.ofNat (j+1)))) requests groups available heap i (j+1) last row data sigs := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · constructor <;> simp (disch := decide) only [store_get_ne,store_get_self] <;>
      first | exact h.outer.requests | exact h.outer.groups | exact h.outer.count | exact h.outer.available | exact h.outer.heap | exact h.outer.index
  all_goals simp (disch := decide) only [store_get_ne,store_get_self]
  all_goals first | exact h.request | exact h.data | exact h.signatures | exact h.last | exact h.index

theorem multiDelegatedAttestVerifyArgs_eval {L imms : Store} {evm : EVM.State} {cd : ByteArray} {root : UInt256}
    {r : DelegatedAttestationRecord} {heap : Nat}
    (hr : L.get? "multiDelegatedRequest"=some (delegatedAttestationTuple cd root))
    (hsc : calldataWord cd root.toNat=r.schema)
    (hd : L.get? "datum"=some r.data.tuple) (hs : L.get? "signature"=some r.signature.tuple)
    (ha : L.get? "attester"=some (.address r.attester)) (hf : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap))) :
    evalExprs? config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestVerifyArgs=
      .ok [r.struct,.int (Int.ofNat heap)] := by
  simp only [multiDelegatedAttestVerifyArgs,evalExprs?,evalExpr?,evalStructFields?,hr,hd,hs,ha,hf,
    delegatedAttestationTuple,DelegatedAttestationRecord.struct,EvalResult.ofOption,bind,EvalResult.bind,pure,hsc]
  rfl

end Benchmarks.EAS.EAS
