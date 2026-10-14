import Benchmarks.CurveVault.Memory
import Benchmarks.CurveVault.ConversionPrefix

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultMaxRedeemArgsMemory (mem : ByteArray) (available : UInt256) : ByteArray :=
  let staged := vaultMaxWord.toByteArray.write 0
    ((⟨0⟩ : UInt256).toByteArray.write 0 (available.toByteArray.write 0 mem 672 32) 704 32) 736 32
  staged.write 672 staged 320 96

theorem vaultMaxRedeemArgsMemory_reads (mem : ByteArray) (available : UInt256) :
    416 ≤ (vaultMaxRedeemArgsMemory mem available).size ∧
    memLoad (UInt256.ofNat 320) (vaultMaxRedeemArgsMemory mem available) = available ∧
    memLoad (UInt256.ofNat 352) (vaultMaxRedeemArgsMemory mem available) = ⟨0⟩ ∧
    memLoad (UInt256.ofNat 384) (vaultMaxRedeemArgsMemory mem available) = vaultMaxWord ∧
    WordMemoryRange mem (vaultMaxRedeemArgsMemory mem available) 576 672 := by
  let mem1 := available.toByteArray.write 0 mem 672 32
  let mem2 := (⟨0⟩ : UInt256).toByteArray.write 0 mem1 704 32
  let staged := vaultMaxWord.toByteArray.write 0 mem2 736 32
  have hgap (d : Nat) (hd : d < 1024) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  have hsize1 : 704 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 672 (hgap _ (by omega) _)
  have hsize2 : 736 ≤ mem2.size := toByteArray_write_size_ge_off_add32 _ _ 704 (hgap _ (by omega) _)
  have hsize3 : 768 ≤ staged.size := toByteArray_write_size_ge_off_add32 _ _ 736 (hgap _ (by omega) _)
  have hsizeCopy := copyWindow_size staged staged 672 320 96 (by omega) (by omega) (by omega)
  have hread (off : Nat) (hoff : off + 32 ≤ 96) :
      memLoad (UInt256.ofNat (320 + off)) (vaultMaxRedeemArgsMemory mem available) =
        memLoad (UInt256.ofNat (672 + off)) staged :=
    memLoad_copyWindow staged staged 672 320 96 off (by omega) (by omega) (by omega) hoff
      (by have : UInt256.size = 2 ^ 256 := rfl; omega) (by have : UInt256.size = 2 ^ 256 := rfl; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change 416 ≤ (staged.write 672 staged 320 96).size
    omega
  · rw [hread 0 (by omega)]
    rw [memLoad_below_write _ _ 736 672 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
      memLoad_below_write _ _ 704 672 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel)]
    exact memLoad_write_back _ _ 672 (by decide +kernel) (hgap _ (by omega) _)
  · rw [hread 32 (by omega)]
    rw [memLoad_below_write _ _ 736 704 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel)]
    exact memLoad_write_back _ _ 704 (by decide +kernel) (hgap _ (by omega) _)
  · rw [hread 64 (by omega)]
    exact memLoad_write_back _ _ 736 (by decide +kernel) (hgap _ (by omega) _)
  · exact (((wordMemoryRange_write mem available 672 576 672 (hgap _ (by omega) _) (Or.inl (by omega))).trans
      (wordMemoryRange_write mem1 ⟨0⟩ 704 576 672 (hgap _ (by omega) _) (Or.inl (by omega)))).trans
      (wordMemoryRange_write mem2 vaultMaxWord 736 576 672 (hgap _ (by omega) _) (Or.inl (by omega)))).trans
      (wordMemoryRange_copy staged staged 672 320 96 576 672 (by omega) (by omega) (by omega) (Or.inr (by omega)))
end Benchmarks.CurveVault
