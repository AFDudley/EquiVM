import Benchmarks.CurveVault.Memory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultConversionArgsMemory (mem : ByteArray) (value flag total : UInt256) : ByteArray :=
  total.toByteArray.write 0 (flag.toByteArray.write 0 (value.toByteArray.write 0 mem 320 32) 352 32) 384 32

theorem vaultConversionArgsMemory_frame (mem : ByteArray) (value flag total : UInt256) :
    WordMemoryRange mem (vaultConversionArgsMemory mem value flag total) 416 UInt256.size := by
  have hgap (m : ByteArray) (off : Nat) (hoff : off ≤ 384) : off - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize off (by omega))
  exact ((wordMemoryRange_write mem value 320 416 UInt256.size (hgap _ _ (by omega)) (Or.inr (by omega))).trans
    (wordMemoryRange_write _ flag 352 416 UInt256.size (hgap _ _ (by omega)) (Or.inr (by omega)))).trans
    (wordMemoryRange_write _ total 384 416 UInt256.size (hgap _ _ (by omega)) (Or.inr (by omega)))

theorem vaultConversionArgsMemory_reads (mem : ByteArray) (value flag total : UInt256) :
    416 ≤ (vaultConversionArgsMemory mem value flag total).size ∧
    memLoad (UInt256.ofNat 320) (vaultConversionArgsMemory mem value flag total) = value ∧
    memLoad (UInt256.ofNat 352) (vaultConversionArgsMemory mem value flag total) = flag ∧
    memLoad (UInt256.ofNat 384) (vaultConversionArgsMemory mem value flag total) = total := by
  let mem1 := value.toByteArray.write 0 mem 320 32
  let mem2 := flag.toByteArray.write 0 mem1 352 32
  have hgap1 : 320 - mem.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 320 (by norm_num))
  have hgap2 : 352 - mem1.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 352 (by norm_num))
  have hgap3 : 384 - mem2.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 384 (by norm_num))
  have hsize1 : 352 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 320 hgap1
  have hsize2 : 384 ≤ mem2.size := toByteArray_write_size_ge_off_add32 _ _ 352 hgap2
  refine ⟨toByteArray_write_size_ge_off_add32 _ _ 384 hgap3, ?_, ?_,
    memLoad_write_back _ _ 384 (by decide +kernel) hgap3⟩
  · change memLoad (UInt256.ofNat 320) (total.toByteArray.write 0 mem2 384 32) = _
    rw [memLoad_below_write _ _ 384 320 (by omega) (by omega) hgap3 (by decide +kernel),
      memLoad_below_write _ _ 352 320 (by omega) (by omega) hgap2 (by decide +kernel)]
    exact memLoad_write_back _ _ 320 (by decide +kernel) hgap1
  · change memLoad (UInt256.ofNat 352) (total.toByteArray.write 0 mem2 384 32) = _
    rw [memLoad_below_write _ _ 384 352 (by omega) (by omega) hgap3 (by decide +kernel)]
    exact memLoad_write_back _ _ 352 (by decide +kernel) hgap2
end Benchmarks.CurveVault
