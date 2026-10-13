import Benchmarks.CurveVault.Memory

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultDebitArguments (mem : ByteArray) (receiver owner : UInt256) : ByteArray :=
  owner.toByteArray.write 0 (receiver.toByteArray.write 0 mem 576 32) 608 32

theorem vaultDebitArguments_reads (mem : ByteArray) (receiver owner : UInt256) :
    640 ≤ (vaultDebitArguments mem receiver owner).size ∧
    memLoad (UInt256.ofNat 576) (vaultDebitArguments mem receiver owner) = receiver ∧
    memLoad (UInt256.ofNat 608) (vaultDebitArguments mem receiver owner) = owner := by
  have hgap (m : ByteArray) (off : Nat) (hsmall : off ≤ 608) : off - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize off (by omega))
  have hs : 608 ≤ (receiver.toByteArray.write 0 mem 576 32).size :=
    toByteArray_write_size_ge_off_add32 _ _ 576 (hgap _ _ (by omega))
  refine ⟨toByteArray_write_size_ge_off_add32 _ _ 608 (hgap _ _ (by omega)), ?_,
    memLoad_write_back _ _ 608 (by decide +kernel) (hgap _ _ (by omega))⟩
  change memLoad (UInt256.ofNat 576) (owner.toByteArray.write 0
    (receiver.toByteArray.write 0 mem 576 32) 608 32) = _
  rw [memLoad_below_write _ _ 608 576 hs (by omega) (hgap _ _ (by omega)) (by decide +kernel)]
  exact memLoad_write_back _ _ 576 (by decide +kernel) (hgap _ _ (by omega))

end Benchmarks.CurveVault
