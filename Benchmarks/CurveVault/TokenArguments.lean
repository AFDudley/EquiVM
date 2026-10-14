import Benchmarks.CurveVault.ApproveArguments

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultTokenArguments (mem : ByteArray) (token sender recipient amount : UInt256) : ByteArray :=
  amount.toByteArray.write 0 (vaultApproveArguments mem token sender recipient) 160 32

theorem vaultTokenArguments_frame (mem : ByteArray) (token sender recipient amount : UInt256) :
    WordMemoryRange mem (vaultTokenArguments mem token sender recipient amount) 192 UInt256.size :=
  ((vaultApproveArguments_frame mem token sender recipient).mono (by omega) (le_refl _)).trans
    (wordMemoryRange_write _ amount 160 192 UInt256.size
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 160 (by omega))) (Or.inr (by omega)))

theorem vaultTokenArguments_reads (mem : ByteArray) (token sender recipient amount : UInt256) :
    192 ≤ (vaultTokenArguments mem token sender recipient amount).size ∧
    memLoad (UInt256.ofNat 64) (vaultTokenArguments mem token sender recipient amount) = token ∧
    memLoad (UInt256.ofNat 96) (vaultTokenArguments mem token sender recipient amount) = sender ∧
    memLoad (UInt256.ofNat 128) (vaultTokenArguments mem token sender recipient amount) = recipient ∧
    memLoad (UInt256.ofNat 160) (vaultTokenArguments mem token sender recipient amount) = amount := by
  obtain ⟨hs, ht, hf, hr⟩ := vaultApproveArguments_reads mem token sender recipient
  have hgap : 160 - (vaultApproveArguments mem token sender recipient).size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 160 (by omega))
  have hframe := wordMemoryRange_write (vaultApproveArguments mem token sender recipient) amount 160 0 160
    hgap (Or.inl (by omega))
  exact ⟨toByteArray_write_size_ge_off_add32 _ _ 160 hgap,
    (hframe.load 64 (by omega) (by omega) (by omega) (by decide +kernel)).trans ht,
    (hframe.load 96 (by omega) (by omega) (by omega) (by decide +kernel)).trans hf,
    (hframe.load 128 (by omega) (by omega) hs (by decide +kernel)).trans hr,
    memLoad_write_back _ _ 160 (by decide +kernel) hgap⟩

end Benchmarks.CurveVault
