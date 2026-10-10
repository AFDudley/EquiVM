import Benchmarks.EAS.EAS.BytesLength
import Benchmarks.EAS.EAS.StoredBytesWrite
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: word arithmetic used by Solidity's bytes storage writer.
theorem bytesWordCount_word (len : UInt256) (hb : len.toNat+31 < UInt256.size) :
    UInt256.shiftRight (len+UInt256.ofNat 31) (UInt256.ofNat 5) =
      UInt256.ofNat (solidityBytesDataWordCount len.toNat) := by
  rw [wordShiftRight_div _ 5 (by decide)]
  apply u256_inj
  rw [udiv_toNat,uadd_word_ofNat_toNat _ _ hb]
  change (len.toNat+31)/32 = (UInt256.ofNat ((len.toNat+31)/32)).toNat
  rw [ulit_toNat' _ (by omega)]

def bytesFirstClear (newLen : Nat) : Nat :=
  if newLen < 32 then 0 else solidityBytesDataWordCount newLen

theorem bytesFirstClear_le {oldLen newLen : Nat} (hl : newLen < oldLen) :
    bytesFirstClear newLen ≤ solidityBytesDataWordCount oldLen := by
  unfold bytesFirstClear solidityBytesDataWordCount
  split <;> omega

theorem bytesClearAccounts_skip (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) (oldLen newLen : Nat)
    (hs : oldLen < 32 ∨ oldLen ≤ newLen) : bytesCleanAccounts σ ee slot oldLen newLen = σ := by
  rcases hs with hs | hs
  · simp only [bytesCleanAccounts,if_pos hs]
  · by_cases ho : oldLen < 32
    · simp only [bytesCleanAccounts,if_pos ho]
    · have hn : ¬newLen < 32 := by omega
      have hc : solidityBytesDataWordCount oldLen - solidityBytesDataWordCount newLen = 0 := by
        unfold solidityBytesDataWordCount
        omega
      simp only [bytesCleanAccounts,if_neg ho,if_neg hn,hc,clearDataWordsForwardFrom]

end Benchmarks.EAS.EAS
