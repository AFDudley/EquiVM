import Benchmarks.CurveVault.Memory
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultInitializeMemory (mem : ByteArray) (amm controller token collateral : UInt256) : ByteArray :=
  writeCascade mem [(64, amm), (96, controller), (128, token), (160, collateral)]

theorem vaultInitializeMemory_facts (mem : ByteArray) (amm controller token collateral : UInt256)
    (hmem : mem.size ≤ 64) :
    (vaultInitializeMemory mem amm controller token collateral).size = 192 ∧
    memLoad (UInt256.ofNat 64) (vaultInitializeMemory mem amm controller token collateral) = amm ∧
    memLoad (UInt256.ofNat 96) (vaultInitializeMemory mem amm controller token collateral) = controller ∧
    memLoad (UInt256.ofNat 128) (vaultInitializeMemory mem amm controller token collateral) = token ∧
    memLoad (UInt256.ofNat 160) (vaultInitializeMemory mem amm controller token collateral) = collateral := by
  have hgap (base : ByteArray) (off : Nat) (hoff : off ≤ 160) : off - base.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize off (by omega))
  have hu := lt_usize 160 (by omega)
  have hsize : (vaultInitializeMemory mem amm controller token collateral).size = 192 := by
    rw [vaultInitializeMemory, writeCascade_size]
    · simp only [writeCascadeSize]; omega
    · simp only [WriteGapsOk, and_true]
      omega
  refine ⟨hsize, ?_, ?_, ?_, ?_⟩
  · exact writeCascade_mload_word_of_head mem 64 (UInt256.ofNat 64) amm
      [(96, controller), (128, token), (160, collateral)] (hgap _ _ (by omega))
      (by simp only [WindowDisjointFromWrites, and_true]; omega) rfl (by change 64 < (vaultInitializeMemory mem amm controller token collateral).size; omega)
  · exact writeCascade_mload_word_of_head (writeWord mem 64 amm) 96 (UInt256.ofNat 96) controller
      [(128, token), (160, collateral)] (hgap _ _ (by omega))
      (by simp only [WindowDisjointFromWrites, and_true]; omega) rfl (by change 96 < (vaultInitializeMemory mem amm controller token collateral).size; omega)
  · exact writeCascade_mload_word_of_head (writeWord (writeWord mem 64 amm) 96 controller) 128 (UInt256.ofNat 128) token
      [(160, collateral)] (hgap _ _ (by omega))
      (by simp only [WindowDisjointFromWrites, and_true]; omega) rfl (by change 128 < (vaultInitializeMemory mem amm controller token collateral).size; omega)
  · exact writeCascade_mload_word_of_head (writeWord (writeWord (writeWord mem 64 amm) 96 controller) 128 token)
      160 (UInt256.ofNat 160) collateral [] (hgap _ _ (by omega)) trivial rfl
      (by change 160 < (vaultInitializeMemory mem amm controller token collateral).size; omega)

end Benchmarks.CurveVault
