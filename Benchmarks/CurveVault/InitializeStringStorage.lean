import Benchmarks.CurveVault.InitializeStorage
import Benchmarks.CurveVault.PaddedReadMemory
import Benchmarks.CurveVault.StringSource

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultStringState (evm : State) (slot : UInt256) (length : Nat) (data : ByteArray) : State :=
  vyperWriteDataWords (Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot (UInt256.ofNat length))
    slot data 0 ((length + 31) / 32)

def vaultStringAccounts (I : ExecutionEnv) (σ : AccountMap) (slot : UInt256)
    (length : Nat) (data : ByteArray) : AccountMap :=
  let σ0 := sstoreAccountMap I.codeOwner σ slot (UInt256.ofNat length)
  let σ1 := sstoreAccountMap I.codeOwner σ0 (slot + ⟨1⟩) (uInt256OfByteArray (data.readWithPadding 0 32))
  if length ≤ 32 then σ1 else
    sstoreAccountMap I.codeOwner σ1 (slot + ⟨2⟩) (uInt256OfByteArray (data.readWithPadding 32 32))

theorem vaultAssignString (isName : Bool) (evm : State) (locals : Store) (length : Nat) (data : ByteArray)
    (hbase : locals.get? (if isName then "name" else "symbol") = none)
    (hcap : length ≤ if isName then 64 else 34) (hdata : data.size = 64) :
    assignStorageRef? config {contract := contract, locals := locals} evm .storage
      {base := if isName then "name" else "symbol", steps := []} (.tuple [.int (Int.ofNat length), .bytes data]) =
      .ok ({contract := contract, locals := locals},
        vaultStringState evm (if isName then ⟨6⟩ else ⟨9⟩) length data) := by
  apply assignStorageRef_storage_of_write (er := {base := if isName then "name" else "symbol", steps := []}) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage {base := if isName then "name" else "symbol", steps := []} =
      some .string by cases isName <;> rfl)
  have hnonneg : ¬ (length : Int) < 0 := Int.not_lt.mpr (Int.natCast_nonneg _)
  cases isName <;> simp only [Bool.false_eq_true, ↓reduceIte] at hcap ⊢ <;>
    simp only [config, storageBackend, Bool.false_eq_true, ↓reduceIte,
      Int.ofNat_eq_natCast, Int.toNat_natCast, hnonneg, decide_false, Bool.false_or, hdata, bne_self_eq_false,
      Bool.or_false, decide_eq_true_eq, not_lt.mpr hcap, vaultStringState, beq_self_eq_true,
      (show ("symbol" == "name") = false from rfl),
      EvalResult.bind, bind, pure] <;> rfl

theorem vaultStringState_source {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (slot : UInt256) (length : Nat) (data : ByteArray)
    (hpos : 0 < length) (hcap : length ≤ 64) :
    SourceState s0 I (vaultStringAccounts I σ slot length data) (vaultStringState evm slot length data) := by
  have hs0 := hs.storageWrite slot (UInt256.ofNat length)
  have hs1 := hs0.storageWrite (slot + ⟨1⟩) (uInt256OfByteArray (data.readWithPadding 0 32))
  by_cases hshort : length ≤ 32
  · have hc : (length + 31) / 32 = 1 := by omega
    simpa only [vaultStringAccounts, if_pos hshort, vaultStringState, hc, vyperWriteDataWords,
      storageStore_executionEnv, hs.env] using hs1
  · have hc : (length + 31) / 32 = 2 := by omega
    have hs2 := hs1.storageWrite (slot + ⟨2⟩) (uInt256OfByteArray (data.readWithPadding 32 32))
    simpa only [vaultStringAccounts, if_neg hshort, vaultStringState, hc, vyperWriteDataWords,
      storageStore_executionEnv, hs.env] using hs2

theorem vaultStringPayload_word (mem data : ByteArray) (off : Nat)
    (hmem : 448 ≤ mem.size) (hoff : off ≤ 32) (hdata : mem.readWithPadding 384 64 = data) :
    memLoad (UInt256.ofNat (384 + off)) mem = uInt256OfByteArray (data.readWithPadding off 32) := by
  have hdata' : mem.extract 384 448 = data := by
    rw [← readWithPadding_eq_extract_unbounded mem 384 64 (by omega) hmem]
    exact hdata
  have hread : data.readWithPadding off 32 = mem.readWithPadding (384 + off) 32 := by
    rw [← hdata']
    exact readWithPadding_extract32 mem 384 448 off
      (by rw [ByteArray.size_extract]; omega) (by omega)
  unfold memLoad
  rw [ulit_toNat' (384 + off) (by change 384 + off < 2 ^ 256; omega),
    if_neg (by omega : ¬ 384 + off ≥ mem.size), ← hread, uInt256OfByteArray_eq]

end Benchmarks.CurveVault
