import Benchmarks.CurveVault.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: a bound on active words survives a bounded memory access.
theorem machineState_M_le {aw off len bound : Nat}
    (haw : aw ≤ bound) (hspan : off + len ≤ 32 * bound) :
    MachineState.M aw off len ≤ bound := by
  unfold MachineState.M
  split
  · exact haw
  · apply max_le haw
    omega

theorem memoryActive_le {aw off len : UInt256} {bound : Nat}
    (haw : aw.toNat ≤ bound) (hspan : off.toNat + len.toNat ≤ 32 * bound) :
    (M aw off len).toNat ≤ bound := by
  exact le_trans (Nat.mod_le _ _) (machineState_M_le haw hspan)

theorem staticCallActive_le {aw inOff inLen outOff outLen : UInt256} {bound : Nat}
    (haw : aw.toNat ≤ bound) (hin : inOff.toNat + inLen.toNat ≤ 32 * bound)
    (hout : outOff.toNat + outLen.toNat ≤ 32 * bound) :
    (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOff.toNat inLen.toNat)
      outOff.toNat outLen.toNat)).toNat ≤ bound := by
  exact le_trans (Nat.mod_le _ _) (machineState_M_le (machineState_M_le haw hin) hout)

-- LIBRARY CANDIDATE: the quadratic memory charge exceeds every UInt256 gas
-- budget when a small memory is expanded to an offset of at least 2^160.
theorem memoryExpansionCost_large {aw off : UInt256}
    (haw : aw.toNat ≤ 12) (hoff : 2 ^ 160 ≤ off.toNat) :
    UInt256.size < memExpansionCost aw off ⟨32⟩ := by
  have hoffMax := off.val.isLt
  have hM : MachineState.M aw.toNat off.toNat 32 < UInt256.size := by
    change max aw.toNat ((off.toNat + 32 + 31) / 32) < UInt256.size
    apply max_lt
    · change aw.toNat < 2 ^ 256
      omega
    · change (off.toNat + 32 + 31) / 32 < 2 ^ 256
      change off.toNat < 2 ^ 256 at hoffMax
      omega
  have hnew : 2 ^ 155 ≤ (M aw off ⟨32⟩).toNat := by
    rw [show (M aw off ⟨32⟩).toNat = MachineState.M aw.toNat off.toNat 32 from
      UInt256.toNat_ofNat_of_lt hM]
    change 2 ^ 155 ≤ max aw.toNat ((off.toNat + 32 + 31) / 32)
    exact le_trans (by omega) (Nat.le_max_right _ _)
  have holdSquare := Nat.mul_self_le_mul_self haw
  have hnewSquare := Nat.mul_self_le_mul_self hnew
  have hquad := Nat.div_le_div_right hnewSquare (c := 512)
  unfold memExpansionCost Cₘ
  change 2 ^ 256 < (3 * (M aw off ⟨32⟩).toNat +
    ((M aw off ⟨32⟩).toNat * (M aw off ⟨32⟩).toNat) / 512) -
    (3 * aw.toNat + aw.toNat * aw.toNat / 512)
  omega

end Benchmarks.CurveVault
