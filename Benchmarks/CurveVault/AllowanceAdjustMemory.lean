import Benchmarks.CurveVault.ApproveInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultAllowanceRawHashMemory (mem : ByteArray) (owner : UInt256) : ByteArray :=
  let first := wordAt0Mem ⟨12⟩ (wordAt32Mem owner mem)
  wordAt0Mem (keccakWord ⟨0⟩ (UInt256.ofNat 64) first)
    (wordAt32Mem (memLoad (UInt256.ofNat 192) first) first)

theorem vaultAllowanceRawHashMemory_eq {mem : ByteArray} {owner spender : UInt256}
    (hsize : 224 ≤ mem.size) (hcanon : owner.toNat < EVM.addressModulus)
    (hspender : memLoad (UInt256.ofNat 192) mem = spender) :
    vaultAllowanceRawHashMemory mem owner = vaultApproveHashMemory mem owner spender := by
  dsimp only [vaultAllowanceRawHashMemory]
  rw [memLoad_vyperHashMem _ _ _ _ (by omega) hsize (by decide +kernel), hspender,
    vyperHashMem_address _ _ _ (by omega) hcanon]
  rfl

theorem vaultApproveHashMemory_size {mem : ByteArray} (owner spender : UInt256) (hsize : 64 ≤ mem.size) :
    (vaultApproveHashMemory mem owner spender).size = mem.size := by
  unfold vaultApproveHashMemory
  rw [vyperHashMem_size _ _ _ (by rw [vyperHashMem_size _ _ _ hsize]; exact hsize),
    vyperHashMem_size _ _ _ hsize]

def vaultAdjustMemory (mem : ByteArray) (owner spender old value : UInt256) : ByteArray :=
  value.toByteArray.write 0 (old.toByteArray.write 0 (vaultApproveHashMemory mem owner spender) 224 32) 256 32

theorem vaultAdjustMemory_reads {mem : ByteArray} {owner spender : UInt256}
    (old value : UInt256) (hsize : 224 ≤ mem.size)
    (hspender : memLoad (UInt256.ofNat 192) mem = spender) :
    288 ≤ (vaultAdjustMemory mem owner spender old value).size ∧
    memLoad (UInt256.ofNat 192) (vaultAdjustMemory mem owner spender old value) = spender ∧
    memLoad (UInt256.ofNat 224) (vaultAdjustMemory mem owner spender old value) = old ∧
    memLoad (UInt256.ofNat 256) (vaultAdjustMemory mem owner spender old value) = value := by
  let base := vaultApproveHashMemory mem owner spender
  let first := old.toByteArray.write 0 base 224 32
  have hgap (d : Nat) (hd : d < 1024) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  have hb : 224 ≤ base.size := by rw [vaultApproveHashMemory_size _ _ (by omega)]; exact hsize
  have hs : 256 ≤ first.size := toByteArray_write_size_ge_off_add32 _ _ 224 (hgap _ (by omega) _)
  refine ⟨toByteArray_write_size_ge_off_add32 _ _ 256 (hgap _ (by omega) _), ?_, ?_, ?_⟩
  · change memLoad (UInt256.ofNat 192) (value.toByteArray.write 0 first 256 32) = _
    rw [memLoad_below_write _ _ 256 192 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
      memLoad_below_write _ _ 224 192 hb (by omega) (hgap _ (by omega) _) (by decide +kernel)]
    unfold base vaultApproveHashMemory
    have hf : (wordAt0Mem ⟨12⟩ (wordAt32Mem owner mem)).size = mem.size :=
      vyperHashMem_size _ _ _ (by omega)
    rw [memLoad_vyperHashMem _ _ _ _ (by omega) (by rw [hf]; exact hsize) (by decide +kernel),
      memLoad_vyperHashMem _ _ _ _ (by omega) hsize (by decide +kernel), hspender]
  · change memLoad (UInt256.ofNat 224) (value.toByteArray.write 0 first 256 32) = _
    rw [memLoad_below_write _ _ 256 224 hs (by omega) (hgap _ (by omega) _) (by decide +kernel)]
    exact memLoad_write_back _ _ 224 (by decide +kernel) (hgap _ (by omega) _)
  · exact memLoad_write_back _ _ 256 (by decide +kernel) (hgap _ (by omega) _)

end Benchmarks.CurveVault
