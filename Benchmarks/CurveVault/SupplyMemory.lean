import Benchmarks.CurveVault.BalanceStorage
import Benchmarks.CurveVault.Memory
import Benchmarks.CurveVault.Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultSupplyMemory (mem : ByteArray) (owner value : UInt256) : ByteArray :=
  value.toByteArray.write 0 (wordAt0Mem ⟨13⟩ (wordAt32Mem owner mem)) 128 32

theorem vaultSupplyMemory_frame (mem : ByteArray) (owner value : UInt256) :
    WordMemoryRange mem (vaultSupplyMemory mem owner value) 160 UInt256.size := by
  exact (wordMemoryRange_vyperHash mem ⟨13⟩ owner 160 UInt256.size (by omega)).trans
    (wordMemoryRange_write _ value 128 160 UInt256.size
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 128 (by omega))) (Or.inr (by omega)))

end Benchmarks.CurveVault
