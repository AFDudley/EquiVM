import Benchmarks.CurveVault.HookMemory
import Benchmarks.CurveVault.MutationSites

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

def vaultHookCachedMemory (flow : VaultFlow) (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray) : ByteArray :=
  match flow with
  | .redeem => (codeOwnerStorageWord I σ (UInt256.ofNat 3)).toByteArray.write 0 mem 704 32
  | _ => mem

def vaultHookAmount (flow : VaultFlow) (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  match flow with
  | .deposit | .withdraw => calldataWord I.calldata 4
  | .mint | .redeem => memLoad (UInt256.ofNat 672) mem

def vaultHookLoadedValue (flow : VaultFlow) (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray) : UInt256 :=
  match flow with
  | .deposit | .withdraw => calldataWord I.calldata 4
  | .mint | .redeem => memLoad (UInt256.ofNat 672)
      (flow.hookSelector.toByteArray.write 0 (vaultHookCachedMemory flow I σ mem) flow.callOffset 32)

def vaultHookCallMemory (flow : VaultFlow) (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (amount : UInt256) : ByteArray :=
  vyperUint256CallMemory (vaultHookCachedMemory flow I σ mem) flow.callOffset flow.hookSelector amount

theorem vaultHookCachedMemory_frame (flow : VaultFlow) (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray) :
    WordMemoryRange mem (vaultHookCachedMemory flow I σ mem) 0 704 := by
  cases flow with
  | deposit | mint | withdraw => exact WordMemoryRange.refl _ _ _
  | redeem =>
    exact wordMemoryRange_write _ _ 704 0 704
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 704 (by omega))) (Or.inl (by omega))

theorem vaultHookLoadedValue_eq (flow : VaultFlow) (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (hsize : 704 ≤ mem.size) : vaultHookLoadedValue flow I σ mem = vaultHookAmount flow I mem := by
  have hframe := (vaultHookCachedMemory_frame flow I σ mem).trans
    (wordMemoryRange_write _ flow.hookSelector flow.callOffset 0 704
      (lt_of_le_of_lt (Nat.sub_le _ _) (by cases flow <;> exact lt_usize _ (by decide +kernel)))
      (Or.inl (by cases flow <;> decide +kernel)))
  cases flow with
  | deposit | withdraw => rfl
  | mint | redeem => exact hframe.load 672 (by omega) (by omega) hsize (by decide +kernel)

theorem vaultHookCallMemory_cachedFrame (flow : VaultFlow) (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (amount : UInt256) :
    WordMemoryRange (vaultHookCachedMemory flow I σ mem) (vaultHookCallMemory flow I σ mem amount) 0 flow.callOffset :=
  vyperUint256CallMemory_frame _ _ _ _ _ _
    (by cases flow <;> exact lt_usize _ (by decide +kernel)) (Or.inl (le_refl _))

theorem vaultHookCallMemory_frame (flow : VaultFlow) (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (amount : UInt256) : WordMemoryRange mem (vaultHookCallMemory flow I σ mem amount) 0 704 :=
  (vaultHookCachedMemory_frame flow I σ mem).trans
    ((vaultHookCallMemory_cachedFrame flow I σ mem amount).mono (by omega) (by cases flow <;> decide +kernel))

theorem vaultHookCallMemory_encode (flow : VaultFlow) (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (amount : UInt256) :
    config.externalABI.encode? flow.hookName [.int (Int.ofNat amount.toNat)] =
      some ((vaultHookCallMemory flow I σ mem amount).readWithPadding (flow.callOffset + 28) 36) := by
  cases flow with
  | deposit | mint =>
    exact vyperUint256CallData (UInt256.ofNat 2762502178) amount
      (selectorBytes 0xa4 0xa8 0x70 0x22) _ 704 (by native_decide) (lt_usize _ (by omega))
  | withdraw | redeem =>
    exact vyperUint256CallData (UInt256.ofNat 1065911937) amount
      (selectorBytes 0x3f 0x88 0x86 0x81) _ 736 (by native_decide) (lt_usize _ (by omega))

end Benchmarks.CurveVault
