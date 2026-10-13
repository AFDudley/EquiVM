import Benchmarks.CurveVault.TokenMemory

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: a bounded CALL output buffer preserves allocated words outside it.
theorem wordMemoryRange_callOutput32 (mem out : ByteArray) (off lo hi : Nat)
    (hout : out.size < UInt256.size) (hoff : off < UInt256.size) (hin : off ≤ mem.size)
    (hdisj : hi ≤ off ∨ off + 32 ≤ lo) :
    WordMemoryRange mem (callOutputMem mem out (UInt256.ofNat off) (UInt256.ofNat 32)) lo hi := by
  unfold callOutputMem
  rw [ulit_toNat' off hoff,
    show (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat = min 32 out.size from callOutputLen32 hout]
  by_cases hz : min 32 out.size = 0
  · rw [hz, byteArray_write_zero_length]
    exact WordMemoryRange.refl _ _ _
  · exact wordMemoryRange_copy out mem 0 off (min 32 out.size) lo hi hz
      (by omega) hin (by rcases hdisj with h | h <;> omega)

def vaultTokenResultMemory (mem out : ByteArray) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0
    (callOutputMem (vaultTokenCallMemory mem) out (UInt256.ofNat 192) (UInt256.ofNat 32)) 320 32

theorem vaultTokenResultMemory_frame (mem out : ByteArray) (hout : out.size < UInt256.size) :
    WordMemoryRange mem (vaultTokenResultMemory mem out) 352 UInt256.size := by
  have hsize := vaultTokenCallMemory_size mem
  exact ((vaultTokenCallMemory_frame mem).mono (by omega) (by omega)).trans
    ((wordMemoryRange_callOutput32 (vaultTokenCallMemory mem) out 192 352 UInt256.size
      hout (by decide +kernel) (by omega) (Or.inr (by omega))).trans
    (wordMemoryRange_write _ (UInt256.ofNat 1) 320 352 UInt256.size
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 320 (by omega))) (Or.inr (by omega))))

end Benchmarks.CurveVault
