import Benchmarks.CurveVault.StringMemory
import Benchmarks.CurveVault.StringEncoding
import Benchmarks.CurveVault.StringGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultStringOutputEmpty (I : ExecutionEnv) (front : ByteArray) (hfront : front.size = 64) :
    encodeReturnValue? .string (.bytes ByteArray.empty) =
      some (vaultStringOutput I (front ++ (UInt256.ofNat 32).toByteArray)) := by
  have hsize : (front ++ (UInt256.ofNat 32).toByteArray).size = 96 := by
    rw [ByteArray.size_append, hfront, toByteArray_size]
  have hload : memLoad ⟨96⟩ (front ++ (UInt256.ofNat 32).toByteArray) = ⟨0⟩ := by
    unfold memLoad
    rw [if_pos (by change 96 ≥ _; omega)]
  have hpadded : vaultStringPaddedMem I (front ++ (UInt256.ofNat 32).toByteArray) =
      front ++ (UInt256.ofNat 32).toByteArray := by
    unfold vaultStringPaddedMem
    rw [hload]
    change I.calldata.write _ _ _ 0 = _
    exact byteArray_write_zero_length _ _ _ _
  rw [stringEmptyReturnEncoding, vaultStringOutput, hpadded, hload]
  change some (_ ++ (UInt256.ofNat 0).toByteArray) =
    some ((front ++ (UInt256.ofNat 32).toByteArray).readWithPadding 64 64)
  have hread : (front ++ (UInt256.ofNat 32).toByteArray).readWithoutPadding 64 64 =
      (UInt256.ofNat 32).toByteArray := by
    unfold ByteArray.readWithoutPadding
    rw [if_neg (by omega), hsize, show min 64 96 = 64 from rfl,
      extract_append_right_window front _ _ _ (by omega), hfront]
    change ((UInt256.ofNat 32).toByteArray).extract 0 64 = _
    apply ByteArray.ext
    simp only [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by change ((UInt256.ofNat 32).toByteArray).size ≤ 64; rw [toByteArray_size]; omega)
  rw [ByteArray.readWithPadding, hread, toByteArray_size]
  have hz : ByteArray.zeroes (64 - 32) = (UInt256.ofNat 0).toByteArray := by decide +kernel
  rw [hz]

def vaultStringClippedHeader (missing : Nat) : ByteArray :=
  (UInt256.ofNat (UInt256.size - missing)).toByteArray.extract 0 (32 - missing) ++ ByteArray.zeroes missing

def vaultStringClippedWord (missing : Nat) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (vaultStringClippedHeader missing))

-- A finite table of the 31 concrete malformed headers that pass the copy-length guard.
-- Only the 32-byte header is evaluated; no large return byte array is constructed.
theorem vaultStringTopOutputTable : ∀ missing : Fin 32, missing.val ≠ 0 →
    maxReturnDataSizeByGas <
      ((⟨32⟩ : UInt256) + UInt256.land
        (⟨32⟩ + vaultStringClippedWord missing.val + ⟨31⟩) (UInt256.lnot ⟨31⟩)).toNat := by
  native_decide

theorem vaultStringClippedHeader_size (missing : Nat) (hmissing : missing ≤ 31) :
    (vaultStringClippedHeader missing).size = 32 := by
  rw [vaultStringClippedHeader, ByteArray.size_append, ByteArray.size_extract,
    toByteArray_size, ByteArray_zeroes_size]
  omega

-- LIBRARY CANDIDATE: load an arbitrary 32-byte suffix immediately after a prefix.
theorem memLoad_append_bytes32 (front bytes : ByteArray) (hfront : front.size < UInt256.size)
    (hbytes : bytes.size = 32) :
    memLoad (UInt256.ofNat front.size) (front ++ bytes) = UInt256.ofNat (fromByteArrayBigEndian bytes) := by
  have hsize : (front ++ bytes).size = front.size + 32 := by rw [ByteArray.size_append, hbytes]
  unfold memLoad
  rw [ulit_toNat' _ hfront, if_neg (by omega),
    readWithPadding_eq_extract_unbounded _ front.size 32 (by omega) (by omega),
    extract_append_right_window front bytes _ _ (by omega)]
  simp only [Nat.sub_self, Nat.add_sub_cancel_left]
  rw [← hbytes, byteArray_extract_self]

theorem vaultStringPaddedTop (I : ExecutionEnv) (front : ByteArray) (length : UInt256)
    (hcd : I.calldata.size < UInt256.size) (hfront : front.size = 96)
    (hlen : UInt256.size - 31 ≤ length.toNat) :
    vaultStringPaddedMem I (front ++ length.toByteArray) =
      front ++ vaultStringClippedHeader (UInt256.size - length.toNat) := by
  let missing := UInt256.size - length.toNat
  have hlt : length.toNat < UInt256.size := length.val.isLt
  have hs : 128 < UInt256.size := by decide +kernel
  have hk : 1 ≤ missing ∧ missing ≤ 31 := by dsimp [missing]; omega
  have hword : length = UInt256.ofNat (UInt256.size - missing) := by
    apply u256_inj
    rw [ulit_toNat' _ (by omega)]
    omega
  have hload : memLoad ⟨96⟩ (front ++ length.toByteArray) = length := by
    have h := memLoad_append_word front ByteArray.empty length (by rw [hfront]; exact lt_trans (by omega) hs)
    rw [hfront, ByteArray.append_empty] at h
    exact h
  have hoff : (UInt256.ofNat 128 + length).toNat = 128 - missing := by
    rw [uadd_toNat]
    change (128 + length.toNat) % UInt256.size = _
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    dsimp [missing]
    omega
  have hpadding : (UInt256.land (UInt256.sub ⟨0⟩ length) ⟨31⟩).toNat = missing := by
    rw [u256_land_31_toNat, usub_toNat_underflow (by change 0 < length.toNat; omega)]
    change (UInt256.size + 0 - length.toNat) % 32 = _
    change missing % 32 = missing
    exact Nat.mod_eq_of_lt (by omega)
  have hsize : (front ++ length.toByteArray).size = 128 := by
    rw [ByteArray.size_append, hfront, toByteArray_size]
  unfold vaultStringPaddedMem
  rw [hload, ulit_toNat' _ hcd, hoff, hpadding, ← hsize,
    byteArray_write_zero_tail _ _ _ _ (by omega) (by omega) (by omega)]
  rw [hsize, extract_append_span front _ _ _ (by omega) (by omega), byteArray_extract_self,
    hfront, show 128 - missing - 96 = 32 - missing by omega, ByteArray.append_assoc]
  change front ++ (length.toByteArray.extract 0 (32 - missing) ++ ByteArray.zeroes missing) =
    front ++ vaultStringClippedHeader missing
  rw [hword]
  rfl

theorem vaultStringOutputTop_large (I : ExecutionEnv) (front : ByteArray) (length : UInt256)
    (hcd : I.calldata.size < UInt256.size) (hfront : front.size = 96)
    (hlen : UInt256.size - 31 ≤ length.toNat) :
    maxReturnDataSizeByGas < (vaultStringOutput I (front ++ length.toByteArray)).size := by
  have hlt : length.toNat < UInt256.size := length.val.isLt
  have hs : 128 < UInt256.size := by decide +kernel
  have hk : 1 ≤ UInt256.size - length.toNat ∧ UInt256.size - length.toNat ≤ 31 := by omega
  have hload := memLoad_append_bytes32 front (vaultStringClippedHeader (UInt256.size - length.toNat))
    (by rw [hfront]; omega) (vaultStringClippedHeader_size _ hk.2)
  rw [hfront] at hload
  change memLoad ⟨96⟩ (front ++ vaultStringClippedHeader (UInt256.size - length.toNat)) =
    vaultStringClippedWord (UInt256.size - length.toNat) at hload
  rw [vaultStringOutput, vaultStringPaddedTop I front length hcd hfront hlen,
    hload, readWithPadding_size]
  exact vaultStringTopOutputTable ⟨UInt256.size - length.toNat, by omega⟩ (by change UInt256.size - length.toNat ≠ 0; omega)

end Benchmarks.CurveVault
