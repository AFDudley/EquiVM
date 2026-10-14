import Benchmarks.EAS.EAS.MultiDelegatedAttestLocals
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestationAttester (cd : ByteArray) (root : UInt256) : AccountAddress :=
  AccountAddress.ofNat (calldataWord cd (root+UInt256.ofNat 96).toNat).toNat

theorem delegatedAttestationAttester_word {cd : ByteArray} {root : UInt256} (ha : delegatedBatchAddressClean cd root) :
    UInt256.ofNat (delegatedAttestationAttester cd root).val=calldataWord cd (root+UInt256.ofNat 96).toNat := by
  have hn : (delegatedAttestationAttester cd root).val=(calldataWord cd (root+UInt256.ofNat 96).toNat).toNat :=
    Nat.mod_eq_of_lt ha
  rw [hn,u256_ofNat_toNat]

theorem multiDelegatedAttestCallArgs_eval {L imms : Store} {evm : EVM.State} {cd : ByteArray} {root available : UInt256}
    {rs : List AttestationRequestRecord} {heap : Nat} {last : Bool}
    (hr : L.get? "multiDelegatedRequest"=some (delegatedAttestationTuple cd root))
    (hd : L.get? "data"=some (.array (rs.map AttestationRequestRecord.tuple)))
    (ha : delegatedBatchAddressClean cd root) (hav : L.get? "availableValue"=some (.int (Int.ofNat available.toNat)))
    (hl : L.get? "last"=some (.bool last)) (hh : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap))) :
    evalExprs? config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestCallArgs=
      .ok [wordBytes32Value (calldataWord cd root.toNat),.array (rs.map AttestationRequestRecord.tuple),
        .address (delegatedAttestationAttester cd root),.int (Int.ofNat available.toNat),.bool last,.int (Int.ofNat heap)] := by
  simp only [multiDelegatedAttestCallArgs,evalExprs?,evalExpr?,hr,hd,hav,hl,hh,delegatedAttestationTuple,
    delegatedAttestationAddressValue,if_pos ha,EvalResult.ofOption,bind,EvalResult.bind,pure]
  rfl

theorem MultiDelegatedAttestLocals.called {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i : Nat} (h : MultiDelegatedAttestLocals L requests groups available heap i)
    (words : List UInt256) (used : UInt256) (next : Nat) :
    MultiDelegatedAttestLocals (multiAttestCallLocals L words used next) requests groups available next i := by
  constructor <;> simp (disch := decide) only [multiAttestCallLocals,heapResultLocals_get,heapResultLocals_heap] <;>
    first | exact h.requests | exact h.groups | exact h.count | exact h.available | exact h.index

theorem MultiDelegatedAttestLocals.next {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i : Nat} (h : MultiDelegatedAttestLocals L requests groups available heap i)
    (words : List UInt256) (used : UInt256) (hi : i<groups.length) (he : groups[i]=[]) :
    MultiDelegatedAttestLocals (multiAttestNextLocals L groups words available used i)
      requests (groups.set i words) (UInt256.sub available used) heap (i+1) := by
  constructor
  · simpa (disch := decide) only [multiAttestNextLocals,store_get_ne] using h.requests
  · simp (disch := decide) only [multiAttestNextLocals,store_get_ne,store_get_self]
  · simp (disch := decide) only [multiAttestNextLocals,store_get_ne,store_get_self,flattenLength_set_empty groups words i hi he]
  · simp (disch := decide) only [multiAttestNextLocals,store_get_ne,store_get_self]
  · simpa (disch := decide) only [multiAttestNextLocals,store_get_ne] using h.heap
  · exact store_get_self _ _ _

end Benchmarks.EAS.EAS
