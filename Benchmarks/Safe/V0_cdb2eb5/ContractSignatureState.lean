import Benchmarks.Safe.V0_cdb2eb5.ContractSignatureTrace
import Benchmarks.Safe.V0_cdb2eb5.BytesMemory
import Benchmarks.Safe.V0_cdb2eb5.ByteCopy

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V0_cdb2eb5

def contractSignatureFinalMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) (out : ByteArray) : ByteArray :=
  signatureReturnMemory (contractSignatureCallMemory mem ptr len hash words)
    ptr out

def contractSignatureNext (ptr len : Nat) (out : ByteArray) : Nat :=
  ptr + ABI.paddedSize out.size

theorem contractSignatureNext_word {ptr len : Nat} {out : ByteArray}
    (hb : ptr + out.size + 31 < UInt256.size) :
    preModuleNextPtr (UInt256.ofNat ptr) out =
      UInt256.ofNat (contractSignatureNext ptr len out) := by
  have hp : ABI.paddedSize out.size ≤ out.size + 31 := by dsimp [ABI.paddedSize]; omega
  have hm : UInt256.land (UInt256.ofNat out.size + UInt256.ofNat 31)
      (UInt256.lnot (UInt256.ofNat 31)) = UInt256.ofNat (ABI.paddedSize out.size) := by
    rw [u256_land_comm]
    apply u256_inj
    change (returnReserveSize out.size).toNat = _
    rw [returnReserveSize_toNat (by omega), ulit_toNat' _ (by omega)]
    simp only [ABI.paddedSize, Nat.mul_comm]
  rw [preModuleNextPtr, hm]
  apply u256_inj
  rw [ulit_toNat' _ (by dsimp [contractSignatureNext]; omega)]
  exact uadd_ofNat_toNat (by omega) (by omega) (by omega)

theorem contractSignatureFinalMemory_free (mem out : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) (hb : ptr + out.size + 31 < UInt256.size) :
    memLoad ⟨64⟩ (contractSignatureFinalMemory mem ptr len hash words out) =
      UInt256.ofNat (contractSignatureNext ptr len out) := by
  rw [contractSignatureFinalMemory, signatureReturnMemory, preModuleReturnFree,
    contractSignatureNext_word hb]

theorem contractSignatureFinalMemory_preserved (mem out : ByteArray) (ptr len off count : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr)
    (hb : ptr < UInt256.size) :
    (contractSignatureFinalMemory mem ptr len hash words out).readWithPadding off count =
      mem.readWithPadding off count := by
  have hm : mem.size ≤
      (preModuleOutputMemory (contractSignatureCallMemory mem ptr len hash words) out
        (UInt256.ofNat ptr)).size := by
    have hg := byteArray_write_size_ge_base out
      (contractSignatureCallMemory mem ptr len hash words) 0 (UInt256.ofNat ptr).toNat
      (min 32 out.size)
    rw [contractSignatureCallMemory_size _ _ _ _ _ hn] at hg
    exact le_trans (Nat.le_max_left _ _) hg
  rw [contractSignatureFinalMemory, signatureReturnMemory, preModuleReturnMemory,
    writeWordReadAbove _ _ _ _ _ (by omega) hl, preModuleOutputMemory,
    ulit_toNat' ptr hb, copyWindowReadBelow _ _ _ _ _ _ _ (by omega)
      (by rw [contractSignatureCallMemory_size _ _ _ _ _ hn]; omega) hh,
    contractSignatureCallMemory_preserved _ _ _ _ _ _ _ hn hin hl hh]

theorem contractSignatureFinalMemory_size (mem out : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) :
    (contractSignatureFinalMemory mem ptr len hash words out).size =
      max mem.size (ptr + 132 + len) := by
  have hpt : (UInt256.ofNat ptr).toNat ≤ ptr := Nat.mod_le _ _
  rw [contractSignatureFinalMemory, signatureReturnMemory, preModuleReturnMemory,
    writeWord_sparse_size, preModuleOutputMemory,
    byteArray_write_size_of_inBounds _ _ _ _ (by omega) (by
      rw [contractSignatureCallMemory_size _ _ _ _ _ hn]; omega),
    contractSignatureCallMemory_size _ _ _ _ _ hn]
  omega

theorem contractSignatureFinalMemory_size_le (mem out : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) (hl : len < 2 ^ 64) (ho : out.size < 2 ^ 138) :
    mem.size ≤ (contractSignatureFinalMemory mem ptr len hash words out).size ∧
      (contractSignatureFinalMemory mem ptr len hash words out).size ≤
        max mem.size (ptr + 2 ^ 140) := by
  rw [contractSignatureFinalMemory_size _ _ _ _ _ _ hn hp]
  omega

theorem contractSignatureNext_bounds (ptr len : Nat) (out : ByteArray)
    (hl : len < 2 ^ 64) (ho : out.size < 2 ^ 138) :
    ptr ≤ contractSignatureNext ptr len out ∧ contractSignatureNext ptr len out ≤ ptr + 2 ^ 140 :=
      by
  dsimp [contractSignatureNext, ABI.paddedSize]
  omega

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

end Benchmarks.Safe.V0_cdb2eb5
