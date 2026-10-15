import Benchmarks.EAS.EAS.RecordFieldExpr
import Benchmarks.EAS.EAS.ResolveOneSource
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure ResolveOneLocals (locals : Store) (a : AttestationRecord) (target : AccountAddress)
    (value available : UInt256) (rev last : Bool) (heap : Nat) : Prop where
  resolver : locals.get? "resolver" = some (.address target)
  attestation : locals.get? "attestation" = some a.value
  value : locals.get? "value" = some (.int (Int.ofNat value.toNat))
  available : locals.get? "availableValue" = some (.int (Int.ofNat available.toNat))
  revocation : locals.get? "isRevocation" = some (.bool rev)
  last : locals.get? "last" = some (.bool last)
  heap : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))

theorem resolveOneLocals_args (record : Value) (a : AttestationRecord) (target : AccountAddress)
    (value available : UInt256) (rev last : Bool) (heap : Nat) :
    ResolveOneLocals ((resolveOneArgs record a value rev available last heap).insert "resolver" (.address target))
      a target value available rev last heap := by
  constructor <;> simp (disch := decide) only [resolveOneArgs, store_get_self, store_get_ne]

theorem resolveOneArgs_field {cfg : Config} {imms : Store} {evm : EVM.State}
    (record : Value) (a : AttestationRecord) (target : AccountAddress)
    (value available : UInt256) (rev last : Bool) (heap : Nat)
    (hr : lookupField? record "resolver" = some (.address target)) :
    evalExpr? cfg {contract := contract, locals := resolveOneArgs record a value rev available last heap, immutables := imms}
      evm (.field (.var "schemaRecord") "resolver") = .ok (.address target) := by
  exact evalRecordField (by simp only [evalExpr?,resolveOneArgs,store_get_self,EvalResult.ofOption]) hr


theorem ResolveOneLocals.payment {locals : Store} {a : AttestationRecord} {target : AccountAddress}
    {value available : UInt256} {rev last : Bool} {heap : Nat}
    (h : ResolveOneLocals locals a target value available rev last heap) (out : ByteArray) :
    ResolveOneLocals (payableProbeLocals locals out heap) a target value available rev last (allocateNext heap 32) := by
  rcases h with ⟨hr,ha,hv,hav,hrv,hl,hh⟩
  constructor <;> simp (disch := decide) only [payableProbeLocals, allocateBlockLocals, unpackHeapLocals, store_get_self, store_get_ne]
  all_goals assumption

theorem ResolveOneLocals.subtract {locals : Store} {a : AttestationRecord} {target : AccountAddress}
    {value available : UInt256} {rev last : Bool} {heap : Nat}
    (h : ResolveOneLocals locals a target value available rev last heap) :
    ResolveOneLocals (locals.insert "availableValue" (.int (Int.ofNat (UInt256.sub available value).toNat)))
      a target value (UInt256.sub available value) rev last heap := by
  rcases h with ⟨hr,ha,hv,hav,hrv,hl,hh⟩
  constructor <;> simp (disch := decide) only [store_get_self, store_get_ne]
  all_goals assumption

theorem ResolveOneLocals.resolved {locals : Store} {a : AttestationRecord} {target : AccountAddress}
    {value available : UInt256} {rev last : Bool} {heap : Nat}
    (h : ResolveOneLocals locals a target value available rev last heap) (out : ByteArray) :
    ResolveOneLocals (resolveOneResolverLocals locals rev heap out)
      a target value available rev last (allocateNext heap (min out.size 32)) := by
  rcases h with ⟨hr,ha,hv,hav,hrv,hl,hh⟩
  cases rev <;> constructor <;>
    simp (disch := decide) only [resolveOneResolverLocals, boolCallBlockLocals, resolveOneCallTmp,
      resolveOneCallResult, Bool.false_eq_true, if_false, if_true, unpackHeapLocals, store_get_self, store_get_ne]
  all_goals assumption

theorem ResolveOneLocals.refunded {locals : Store} {a : AttestationRecord} {target : AccountAddress}
    {value available : UInt256} {rev last : Bool} {heap : Nat}
    (h : ResolveOneLocals locals a target value available rev last heap) (heap' : Nat) :
    ResolveOneLocals (resolveOneRefundLocals locals heap') a target value available rev last heap' := by
  rcases h with ⟨hr,ha,hv,hav,hrv,hl,hh⟩
  constructor <;> simp (disch := decide) only [resolveOneRefundLocals, unpackHeapLocals, store_get_self, store_get_ne]
  all_goals assumption

end Benchmarks.EAS.EAS
