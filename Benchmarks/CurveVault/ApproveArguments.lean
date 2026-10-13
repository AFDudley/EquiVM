import Benchmarks.CurveVault.Memory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultApproveArguments (mem : ByteArray) (owner spender value : UInt256) : ByteArray :=
  value.toByteArray.write 0 (spender.toByteArray.write 0 (owner.toByteArray.write 0 mem 64 32) 96 32) 128 32

theorem vaultApproveArguments_frame (mem : ByteArray) (owner spender value : UInt256) :
    WordMemoryRange mem (vaultApproveArguments mem owner spender value) 160 UInt256.size := by
  have hgap (d : Nat) (hd : d ≤ 128) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  exact (wordMemoryRange_write mem owner 64 160 UInt256.size (hgap _ (by omega) _) (Or.inr (by omega))).trans
    ((wordMemoryRange_write _ spender 96 160 UInt256.size (hgap _ (by omega) _) (Or.inr (by omega))).trans
      (wordMemoryRange_write _ value 128 160 UInt256.size (hgap _ (by omega) _) (Or.inr (by omega))))

theorem vaultApproveArguments_reads (mem : ByteArray) (owner spender value : UInt256) :
    160 ≤ (vaultApproveArguments mem owner spender value).size ∧
    memLoad (UInt256.ofNat 64) (vaultApproveArguments mem owner spender value) = owner ∧
    memLoad (UInt256.ofNat 96) (vaultApproveArguments mem owner spender value) = spender ∧
    memLoad (UInt256.ofNat 128) (vaultApproveArguments mem owner spender value) = value := by
  have hgap (d : Nat) (hd : d < 1024) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  let mem0 := owner.toByteArray.write 0 mem 64 32
  let mem1 := spender.toByteArray.write 0 mem0 96 32
  have hs0 : 96 ≤ mem0.size := toByteArray_write_size_ge_off_add32 _ _ 64 (hgap _ (by omega) _)
  have hs1 : 128 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 96 (hgap _ (by omega) _)
  refine ⟨toByteArray_write_size_ge_off_add32 _ _ 128 (hgap _ (by omega) _), ?_, ?_, ?_⟩
  · change memLoad (UInt256.ofNat 64) (value.toByteArray.write 0 mem1 128 32) = _
    rw [memLoad_below_write _ _ 128 64 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
      memLoad_below_write _ _ 96 64 hs0 (by omega) (hgap _ (by omega) _) (by decide +kernel)]
    exact memLoad_write_back _ _ 64 (by decide +kernel) (hgap _ (by omega) _)
  · change memLoad (UInt256.ofNat 96) (value.toByteArray.write 0 mem1 128 32) = _
    rw [memLoad_below_write _ _ 128 96 hs1 (by omega) (hgap _ (by omega) _) (by decide +kernel)]
    exact memLoad_write_back _ _ 96 (by decide +kernel) (hgap _ (by omega) _)
  · exact memLoad_write_back _ _ 128 (by decide +kernel) (hgap _ (by omega) _)

end Benchmarks.CurveVault
