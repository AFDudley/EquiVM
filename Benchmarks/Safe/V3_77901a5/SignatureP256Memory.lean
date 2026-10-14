import Benchmarks.Safe.V3_77901a5.SignatureP256Source
import Benchmarks.Safe.V3_77901a5.BytesMemory

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V3_77901a5

set_option maxHeartbeats 800000

theorem signatureP256Address {src : Nat} {s : UInt256} (j : Nat)
    (hb : src + s.toNat + j < UInt256.size) :
    (UInt256.ofNat src + s) + UInt256.ofNat j = UInt256.ofNat (src + s.toNat + j) := by
  apply u256_inj
  change ((src % UInt256.size + s.toNat) % UInt256.size + j % UInt256.size) % UInt256.size = _
  rw [Nat.mod_eq_of_lt (by omega : src < UInt256.size),
    Nat.mod_eq_of_lt (by omega : src + s.toNat < UInt256.size),
    Nat.mod_eq_of_lt (by omega : j < UInt256.size)]
  rfl

theorem signatureP256Word {p : SignatureInput} {mem : ByteArray} {src : Nat} {s : UInt256}
    (hm : BytesMemory mem src p.signatures) (hh : s.toNat + 128 ≤ p.signatures.size)
    (hb : src + 64 + p.signatures.size < UInt256.size) (j : Nat) (hj : j ≤ 96) :
    memLoad ((UInt256.ofNat src + s) + UInt256.ofNat (32 + j)) mem =
      calldataWord p.signatures (s.toNat + j) := by
  rw [signatureP256Address _ (by omega)]
  have he : src + s.toNat + (32 + j) = src + 32 + (s.toNat + j) := by omega
  rw [he]
  exact hm.word (by omega) (by omega)

theorem signatureP256Hash {p : SignatureInput} {mem : ByteArray} {src : Nat} {s : UInt256}
    (hm : BytesMemory mem src p.signatures) (hh : s.toNat + 128 ≤ p.signatures.size)
    (hb : src + 64 + p.signatures.size < UInt256.size) :
    keccakWord ((UInt256.ofNat src + s) + UInt256.ofNat 96) (UInt256.ofNat 64) mem =
      p256SignerWord (signatureP256Input p s) := by
  have hr (j : Nat) (hj : j ≤ 96) :
      mem.readWithPadding (src + 32 + (s.toNat + j)) 32 =
        (calldataWord p.signatures (s.toNat + j)).toByteArray := by
    have h := hm.word (off := s.toNat + j) (by omega) (by omega)
    rw [memLoadReadWord, ulit_toNat' _ (by omega)] at h
    rw [← h, toByteArray_uInt256OfByteArray_of_size32 (paddedReadSize _ _ _)]
  simp only [keccakWord, keccakSlot_eq, p256SignerWord]
  apply congrArg uInt256OfByteArray
  apply congrArg KEC
  rw [signatureP256Address _ (by omega), ulit_toNat' _ (by omega)]
  have ha : src + s.toNat + 96 = src + 32 + (s.toNat + 64) := by omega
  have ha' : src + 32 + (s.toNat + 64) + 32 = src + 32 + (s.toNat + 96) := by omega
  change mem.readWithPadding (src + s.toNat + 96) 64 = _
  rw [ha, show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide)
      (by have := hm.available; omega), hr 64 (by decide), ha', hr 96 (by decide)]
  simp [wordBytes, signatureP256Input]

end Benchmarks.Safe.V3_77901a5
