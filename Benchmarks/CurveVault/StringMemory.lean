import Benchmarks.CurveVault.StringLoop
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: a sequence of Vyper data words has a fixed byte length.
theorem vyperReadDataWords_size (evm : State) (slot : UInt256) (index count : Nat) :
    (vyperReadDataWords evm slot index count).size = 32 * count := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      rw [vyperReadDataWords, ByteArray.size_append, toByteArray_size, ih]
      omega

theorem vaultStringCopyWord_append (I : ExecutionEnv) (σ : AccountMap) (slot : UInt256)
    (mem : ByteArray) (index : Nat) (hindex : index ≤ 3) (hsize : mem.size = 96 + 32 * index) :
    vaultStringCopyWord I σ slot (UInt256.ofNat index) mem =
      mem ++ (codeOwnerStorageWord I σ (slot + UInt256.ofNat index)).toByteArray := by
  have hoff : (UInt256.ofNat 96 + UInt256.shiftLeft (UInt256.ofNat index) (UInt256.ofNat 5)).toNat = 96 + 32 * index := by
    change (UInt256.ofNat 96 + UInt256.shiftLeft (UInt256.ofNat index) ⟨5⟩).toNat = _
    rw [uadd_toNat, ushl5_ofNat_toNat index (by omega)]
    change (96 + 32 * index) % UInt256.size = _
    exact Nat.mod_eq_of_lt (by change 96 + 32 * index < 2 ^ 256; omega)
  unfold vaultStringCopyWord
  rw [hoff, ← hsize, write_at_end_eq _ _ 32 (by omega) (by rw [toByteArray_size]), toByteArray_extract0_32]

theorem vaultStringCopyMemory_data {s0 : State} {I : ExecutionEnv} {σ : AccountMap} {evm : State}
    (hs : SourceState s0 I σ evm) (slot : UInt256) (count : Nat) :
    ∀ (index : Nat) (mem : ByteArray), index + count ≤ 2 → mem.size = 128 + 32 * index →
      vaultStringCopyMemory I σ slot mem (index + 1) count = mem ++ vyperReadDataWords evm slot index count := by
  induction count with
  | zero =>
      intro index mem hbound hsize
      simp only [vaultStringCopyMemory, vyperReadDataWords, ByteArray.append_empty]
  | succ count ih =>
      intro index mem hbound hsize
      have hcopy := vaultStringCopyWord_append I σ slot mem (index + 1) (by omega) (by omega)
      rw [vaultStringCopyMemory, hcopy]
      have hm : (mem ++ (codeOwnerStorageWord I σ (slot + UInt256.ofNat (index + 1))).toByteArray).size =
          128 + 32 * (index + 1) := by rw [ByteArray.size_append, toByteArray_size, hsize]; omega
      rw [ih (index + 1) _ (by omega) hm, vyperReadDataWords]
      rw [hs.storageRead, show 1 + index = index + 1 by omega]
      exact ByteArray.append_assoc

theorem vaultStringCopyMemory_header {s0 : State} {I : ExecutionEnv} {σ : AccountMap} {evm : State}
    (hs : SourceState s0 I σ evm) (slot : UInt256) (mem : ByteArray) (count : Nat)
    (hsize : mem.size = 96) (hcount : count ≤ 2) :
    vaultStringCopyMemory I σ slot mem 0 (count + 1) =
      (mem ++ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toByteArray) ++
        vyperReadDataWords evm slot 0 count := by
  rw [vaultStringCopyMemory, vaultStringCopyWord_append I σ slot mem 0 (by omega) (by omega)]
  change vaultStringCopyMemory I σ slot (mem ++ (codeOwnerStorageWord I σ (slot + ⟨0⟩)).toByteArray) 1 count = _
  rw [uint256_add_zero_right]
  rw [vaultStringCopyMemory_data hs slot count 0 _ (by omega) (by rw [ByteArray.size_append, toByteArray_size, hsize])]
  rw [hs.storageRead]

-- LIBRARY CANDIDATE: loading the word immediately after any memory prefix.
theorem memLoad_append_word (front suffix : ByteArray) (word : UInt256)
    (hfront : front.size < UInt256.size) :
    memLoad (UInt256.ofNat front.size) ((front ++ word.toByteArray) ++ suffix) = word := by
  have hsize : front.size + 32 ≤ ((front ++ word.toByteArray) ++ suffix).size := by
    rw [ByteArray.size_append, ByteArray.size_append, toByteArray_size]
    omega
  unfold memLoad
  rw [ulit_toNat' front.size hfront, if_neg (by omega),
    readWithPadding_eq_extract_unbounded _ front.size 32 (by omega) hsize]
  rw [extract_append_left (front ++ word.toByteArray) suffix _ _ (by rw [ByteArray.size_append, toByteArray_size]),
    extract_append_right_window front word.toByteArray _ _ (le_refl _)]
  simp only [Nat.sub_self, Nat.add_sub_cancel_left, toByteArray_extract0_32]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

-- LIBRARY CANDIDATE: copying beyond calldata clears an existing memory suffix.
theorem byteArray_write_zero_tail (src mem : ByteArray) (srcOff length : Nat)
    (hsrc : src.size ≤ srcOff) (hlen : length ≤ mem.size) (hsmall : length < 2 ^ 32) :
    src.write srcOff mem (mem.size - length) length = mem.extract 0 (mem.size - length) ++ ByteArray.zeroes length := by
  by_cases hz : length = 0
  · subst length
    rw [byteArray_write_zero_length, Nat.sub_zero, byteArray_extract_self, zeroes_zero (n := 0) rfl, ByteArray.append_empty]
  have hzero : (ByteArray.zeroes length).data.size = length := zeroes_ofNat_size length hsmall
  unfold ByteArray.write
  rw [if_neg hz, if_pos hsrc, Nat.min_eq_left (by omega : length ≤ mem.size - (mem.size - length)),
    Nat.min_eq_left (Nat.sub_le _ _)]
  apply ByteArray.ext
  simp only [ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract,
    hzero, Nat.sub_zero, Nat.min_self, Nat.zero_add]
  rw [Array.extract_eq_self_of_le (by omega : (ByteArray.zeroes length).data.size ≤ length)]
  rw [show mem.data.extract (mem.size - length + length) = #[] from by
    apply Array.extract_eq_empty_of_le
    simp only [Nat.min_self]
    change mem.size ≤ mem.size - length + length
    omega]
  simp only [Array.append_empty]

end Benchmarks.CurveVault
