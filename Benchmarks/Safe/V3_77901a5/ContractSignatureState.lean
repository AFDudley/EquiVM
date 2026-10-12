import Benchmarks.Safe.V3_77901a5.ContractSignatureTrace
import Benchmarks.Safe.V3_77901a5.BytesMemory
import Benchmarks.Safe.V3_77901a5.ByteCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V3_77901a5

def contractSignatureFinalMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) (out : ByteArray) : ByteArray :=
  signatureReturnMemory (contractSignatureCallMemory mem ptr len hash words)
    (contractSignatureCallEnd ptr len) out

def contractSignatureNext (ptr len : Nat) (out : ByteArray) : Nat :=
  if out.size = 0 then contractSignatureCallEnd ptr len
  else contractSignatureCallEnd ptr len + 32 + ABI.paddedSize out.size

theorem contractSignatureFinalMemory_free (mem out : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) (hb : ptr + out.size + 31 < UInt256.size) :
    memLoad ⟨64⟩ (contractSignatureFinalMemory mem ptr len hash words out) =
      UInt256.ofNat (contractSignatureNext ptr len out) := by
  by_cases hz : out.size = 0
  · simp only [contractSignatureFinalMemory, signatureReturnMemory, contractSignatureNext,
      hz, if_true]
    rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
      contractSignatureCallMemory, rawBytesCopyMemory_preserved _ _ _ _ _ _
        (contractSignatureBufferMemory_end _ _ _ _ _ hn)
        (by rw [contractSignatureBufferMemory_size _ _ _ _ _ hn]; omega)
        (by dsimp [contractSignatureCallEnd]; omega),
      ← show (⟨64⟩ : UInt256).toNat = 64 from rfl, ← memLoadReadWord,
      contractSignatureBufferMemory_free _ _ _ _ _ hn hp]
  · simp only [contractSignatureFinalMemory, signatureReturnMemory, contractSignatureNext,
      hz, if_false]
    exact returnDataMemory_free _ _ _ (by dsimp [contractSignatureCallEnd]; omega)

theorem contractSignatureFinalMemory_preserved (mem out : ByteArray) (ptr len off count : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr)
    (hb : ptr < UInt256.size) :
    (contractSignatureFinalMemory mem ptr len hash words out).readWithPadding off count =
      mem.readWithPadding off count := by
  by_cases hz : out.size = 0
  · simp only [contractSignatureFinalMemory, signatureReturnMemory, hz, if_true]
    exact contractSignatureCallMemory_preserved _ _ _ _ _ _ _ hn hin hl hh
  · simp only [contractSignatureFinalMemory, signatureReturnMemory, hz, if_false]
    rw [returnDataMemory_preserved _ _ _ _ _
      (by rw [contractSignatureCallMemory_size _ _ _ _ _ hn]; omega) hl
      (by dsimp [contractSignatureCallEnd]; omega),
      contractSignatureCallMemory_preserved _ _ _ _ _ _ _ hn hin hl hh]

theorem contractSignatureFinalMemory_size (mem out : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) :
    (contractSignatureFinalMemory mem ptr len hash words out).size =
      max mem.size (max (ptr + 264 + 2 * ABI.paddedSize len)
        (contractSignatureCallEnd ptr len + 32 + out.size)) := by
  by_cases hz : out.size = 0
  · simp only [contractSignatureFinalMemory, signatureReturnMemory, hz, if_true,
      contractSignatureCallMemory_size _ _ _ _ _ hn]
    dsimp [contractSignatureCallEnd, contractSignatureCallLength]
    congr 1
    omega
  · simp only [contractSignatureFinalMemory, signatureReturnMemory, hz, if_false]
    rw [returnDataMemory_size _ _ _ (by dsimp [contractSignatureCallEnd]; omega),
      contractSignatureCallMemory_size _ _ _ _ _ hn]
    omega

theorem contractSignatureFinalMemory_size_le (mem out : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) (hl : len < 2 ^ 64) (ho : out.size < 2 ^ 138) :
    mem.size ≤ (contractSignatureFinalMemory mem ptr len hash words out).size ∧
      (contractSignatureFinalMemory mem ptr len hash words out).size ≤
        max mem.size (ptr + 2 ^ 140) := by
  rw [contractSignatureFinalMemory_size _ _ _ _ _ _ hn hp]
  dsimp [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize]
  omega

theorem contractSignatureNext_bounds (ptr len : Nat) (out : ByteArray)
    (hl : len < 2 ^ 64) (ho : out.size < 2 ^ 138) :
    ptr ≤ contractSignatureNext ptr len out ∧ contractSignatureNext ptr len out ≤ ptr + 2 ^ 140 := by
  dsimp [contractSignatureNext, contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize]
  split <;> omega

theorem contractSignatureFinalMemory_bytes {mem out bytes : ByteArray} {ptr len src : Nat}
    {hash : UInt256} {words : List UInt256} (hn : words.length = (len + 31) / 32)
    (hbytes : BytesMemory mem src bytes) (hs : 96 ≤ src) (ha : src + 32 + bytes.size ≤ ptr)
    (hb : src < UInt256.size) (hp : ptr < UInt256.size) :
    BytesMemory (contractSignatureFinalMemory mem ptr len hash words out) src bytes := by
  refine ⟨?_, ?_, ?_⟩
  · rw [memLoadReadWord, ulit_toNat' src hb,
      contractSignatureFinalMemory_preserved _ _ _ _ _ _ _ _ hn (by
        have := hbytes.available; omega) hs (by omega) hp,
      ← ulit_toNat' src hb, ← memLoadReadWord, hbytes.length]
  · rw [contractSignatureFinalMemory_preserved _ _ _ _ _ _ _ _ hn (by
      have := hbytes.available; omega) (by omega) ha hp, hbytes.payload]
  · have hh : mem.size ≤ (contractSignatureFinalMemory mem ptr len hash words out).size := by
      rw [contractSignatureFinalMemory_size _ _ _ _ _ _ hn (by omega)]
      omega
    have := hbytes.available
    omega

end Benchmarks.Safe.V3_77901a5
