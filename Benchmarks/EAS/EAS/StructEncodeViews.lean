import Benchmarks.EAS.EAS.StructEncode
import Benchmarks.EAS.EAS.CopyEncodeViews
import Benchmarks.EAS.EAS.PayloadViews
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem writeWordSequence_read_below_len (mem : ByteArray) (off read len : Nat) (ws : List UInt256)
    (hhi : read+len ≤ off) (hin : read+len ≤ mem.size) :
    (writeWordSequence mem off ws).readWithPadding read len = mem.readWithPadding read len := by
  induction ws generalizing mem off with
  | nil => rfl
  | cons w ws ih =>
    rw [writeWordSequence, ih _ _ (by omega) (by rw [writeWord_sparse_size]; omega),
      writeWord_read_below_len _ _ _ _ _ hhi hin]

theorem memoryPrefix_read_words {before after : ByteArray} {limit : Nat}
    (hp : MemoryPrefix before after limit) (off n : Nat) (hlo : 96 ≤ off)
    (hhi : off+32*n ≤ limit) (hin : off+32*n ≤ before.size) (hbound : off+32*n < UInt256.size) :
    after.readWithPadding off (32*n) = before.readWithPadding off (32*n) := by
  rw [← memoryWords_bytes _ _ _ hbound (le_trans hin hp.size),
    memoryWords_prefix hp off n hlo hhi hin hbound, memoryWords_bytes _ _ _ hbound hin]

theorem copyStoredOutputMemory_loadField (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hg : allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320)
    (hlo : 96 ≤ heap.toNat) (i : Nat) (hi : i < 9) :
    memLoad (heap+UInt256.ofNat (32*i)) (copyStoredOutputMemory evm word heap mem) =
      (storedAttestationWords evm.accountMap evm.executionEnv (dbSlot word))[i]'(by
        simpa only [storedAttestationWords, List.length_cons, List.length_nil] using hi) := by
  have hb := (allocate320_bounds hg).2
  have hs : (heap+UInt256.ofNat (32*i)).toNat = heap.toNat+32*i :=
    uadd_word_ofNat_toNat heap (32*i) (by change heap.toNat+32*i < 2^256; omega)
  apply mloadWordValue_of_readWithPadding
  · rw [hs, copyStoredOutputMemory, writeWord_sparse_size]
    omega
  · rw [hs]
    exact copyStoredOutputMemory_field evm word heap mem hg hlo i hi

theorem copyStoredOutputMemory_loadDataPointer (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hg : allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320) :
    memLoad (heap+UInt256.ofNat 288) (copyStoredOutputMemory evm word heap mem) = copyStoredBytePtr heap := by
  have hb := (allocate320_bounds hg).2
  have hs : (heap+UInt256.ofNat 288).toNat = heap.toNat+288 :=
    uadd_word_ofNat_toNat heap 288 (by change heap.toNat+288 < 2^256; omega)
  apply mloadWordValue_of_readWithPadding
  · rw [hs, copyStoredOutputMemory, writeWord_sparse_size]
    omega
  · rw [hs]
    exact copyStoredOutputMemory_dataPointer evm word heap mem

theorem boolCleanup_idempotent (word : UInt256) :
    UInt256.isZero (UInt256.isZero (UInt256.isZero (UInt256.isZero word))) = UInt256.isZero (UInt256.isZero word) := by
  by_cases hz : word = ⟨0⟩
  · rw [hz]; decide
  · rw [isZero_eq_zero_of_ne hz]; decide

theorem copyStoredOutputMemory_headWords (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hg : allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320)
    (hlo : 96 ≤ heap.toNat) :
    attestationEncodeHeadWords (copyStoredOutputMemory evm word heap mem) heap =
      storedAttestationWords evm.accountMap evm.executionEnv (dbSlot word) ++ [UInt256.ofNat 320] := by
  have h (i : Nat) (hi : i < 9) := copyStoredOutputMemory_loadField evm word heap mem hg hlo i hi
  have h0 := h 0 (by decide)
  have hz : heap+UInt256.ofNat 0 = heap := u256_add_zero heap
  simp only [Nat.mul_zero, hz] at h0
  have h64 : UInt256.ofNat (2^64-1) = (⟨18446744073709551615⟩ : UInt256) := rfl
  have h160 : UInt256.ofNat (2^160-1) = (⟨1461501637330902918203684832716283019655932542975⟩ : UInt256) := rfl
  simp only [attestationEncodeHeadWords, attestationEncodeFirstWords, attestationEncodeLastWords,
    h0, h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
  simp only [storedAttestationWords, List.getElem_cons_zero, List.getElem_cons_succ,
    h64, h160, maskTwice, boolCleanup_idempotent]
  rfl

theorem attestationHeadWords_of_prefix {before after : ByteArray} {limit : Nat} (hp : MemoryPrefix before after limit)
    (src : UInt256) (hlo : 96 ≤ src.toNat) (hhi : src.toNat+320 ≤ limit)
    (hin : src.toNat+320 ≤ before.size) (hbound : src.toNat+320 < UInt256.size) :
    attestationEncodeHeadWords after src = attestationEncodeHeadWords before src := by
  have hr (n : Nat) (hn : n+32 ≤ 320) : memLoad (src+UInt256.ofNat n) after = memLoad (src+UInt256.ofNat n) before := by
    have hs : (src+UInt256.ofNat n).toNat = src.toNat+n := uadd_word_ofNat_toNat src n (by omega)
    exact memLoad_of_prefix hp _ (by rw [hs]; omega) (by rw [hs]; omega) (by rw [hs]; omega)
  have h0 := memLoad_of_prefix hp src hlo (by omega) (by omega)
  simp only [attestationEncodeHeadWords, attestationEncodeFirstWords, attestationEncodeLastWords,
    h0, hr 32 (by decide), hr 64 (by decide), hr 96 (by decide), hr 128 (by decide),
    hr 160 (by decide), hr 192 (by decide), hr 224 (by decide), hr 256 (by decide)]

end Benchmarks.EAS.EAS
