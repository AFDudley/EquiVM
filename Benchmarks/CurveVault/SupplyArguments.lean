import Benchmarks.CurveVault.Memory

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultSupplyArguments (mem : ByteArray) (owner value : UInt256) : ByteArray :=
  value.toByteArray.write 0 (owner.toByteArray.write 0 mem 64 32) 96 32

theorem vaultSupplyArguments_frame (mem : ByteArray) (owner value : UInt256) :
    WordMemoryRange mem (vaultSupplyArguments mem owner value) 128 UInt256.size :=
  (wordMemoryRange_write mem owner 64 128 UInt256.size
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by omega))) (Or.inr (by omega))).trans
    (wordMemoryRange_write _ value 96 128 UInt256.size
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 96 (by omega))) (Or.inr (by omega)))

theorem vaultSupplyArguments_reads (mem : ByteArray) (owner value : UInt256) :
    128 ≤ (vaultSupplyArguments mem owner value).size ∧
    memLoad (UInt256.ofNat 64) (vaultSupplyArguments mem owner value) = owner ∧
    memLoad (UInt256.ofNat 96) (vaultSupplyArguments mem owner value) = value := by
  have hgap (m : ByteArray) (off : Nat) (hsmall : off ≤ 96) : off - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize off (by omega))
  have hs : 96 ≤ (owner.toByteArray.write 0 mem 64 32).size :=
    toByteArray_write_size_ge_off_add32 _ _ 64 (hgap _ _ (by omega))
  refine ⟨toByteArray_write_size_ge_off_add32 _ _ 96 (hgap _ _ (by omega)), ?_,
    memLoad_write_back _ _ 96 (by decide +kernel) (hgap _ _ (by omega))⟩
  change memLoad (UInt256.ofNat 64) (value.toByteArray.write 0 (owner.toByteArray.write 0 mem 64 32) 96 32) = _
  rw [memLoad_below_write _ _ 96 64 hs (by omega) (hgap _ _ (by omega)) (by decide +kernel)]
  exact memLoad_write_back _ _ 64 (by decide +kernel) (hgap _ _ (by omega))

end Benchmarks.CurveVault
