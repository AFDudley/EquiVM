import Benchmarks.CurveVault.StringMemory
import Benchmarks.CurveVault.StringEncoding

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultStringPaddedNormal (I : ExecutionEnv) (front data : ByteArray) (length : UInt256)
    (hcd : I.calldata.size < UInt256.size) (hfront : front.size = 96)
    (hlen : length.toNat ≤ 64) (hdata : data.size = ABI.paddedSize length.toNat) :
    vaultStringPaddedMem I ((front ++ length.toByteArray) ++ data) =
      ((front ++ length.toByteArray) ++ data.extract 0 length.toNat) ++
        ByteArray.zeroes (ABI.paddedSize length.toNat - length.toNat) := by
  have hload : memLoad ⟨96⟩ ((front ++ length.toByteArray) ++ data) = length := by
    have h := memLoad_append_word front data length (by rw [hfront]; decide +kernel)
    rw [hfront] at h
    exact h
  have hpad : length.toNat ≤ ABI.paddedSize length.toNat := by
    change length.toNat ≤ 32 * ((length.toNat + 31) / 32)
    omega
  have hpads : ABI.paddedSize length.toNat ≤ 64 := by
    change 32 * ((length.toNat + 31) / 32) ≤ 64
    omega
  have hhead : (front ++ length.toByteArray).size = 128 := by
    rw [ByteArray.size_append, hfront, toByteArray_size]
  have hsize : ((front ++ length.toByteArray) ++ data).size = 128 + ABI.paddedSize length.toNat := by
    rw [ByteArray.size_append, hhead, hdata]
  have hoff : (UInt256.ofNat 128 + length).toNat = 128 + length.toNat := by
    rw [uadd_toNat]
    change (128 + length.toNat) % UInt256.size = _
    exact Nat.mod_eq_of_lt (by change 128 + length.toNat < 2 ^ 256; omega)
  unfold vaultStringPaddedMem
  rw [hload, ulit_toNat' _ hcd, hoff, vyperStringPadding_toNat length hlen]
  have hdest : 128 + length.toNat = ((front ++ length.toByteArray) ++ data).size -
      (ABI.paddedSize length.toNat - length.toNat) := by rw [hsize]; omega
  rw [hdest, byteArray_write_zero_tail _ _ _ _ (by omega) (by rw [hsize]; omega) (by omega)]
  rw [← hdest, extract_append_span _ _ _ _ (by omega) (by rw [hhead]; omega),
    byteArray_extract_self, hhead, Nat.add_sub_cancel_left]

theorem vaultStringOutputNormal (I : ExecutionEnv) (front data : ByteArray) (length : UInt256)
    (hcd : I.calldata.size < UInt256.size) (hfront : front.size = 64)
    (hlen : length.toNat ≤ 64) (hdata : data.size = ABI.paddedSize length.toNat) :
    encodeReturnValue? .string (.bytes (data.extract 0 length.toNat)) =
      some (vaultStringOutput I (((front ++ (UInt256.ofNat 32).toByteArray) ++ length.toByteArray) ++ data)) := by
  have hhead : (front ++ (UInt256.ofNat 32).toByteArray).size = 96 := by
    rw [ByteArray.size_append, hfront, toByteArray_size]
  have hpad : length.toNat ≤ ABI.paddedSize length.toNat := by
    change length.toNat ≤ 32 * ((length.toNat + 31) / 32)
    omega
  have hbytes : (data.extract 0 length.toNat).size = length.toNat := by
    rw [ByteArray.size_extract, hdata]
    omega
  have hpadded := vaultStringPaddedNormal I (front ++ (UInt256.ofNat 32).toByteArray)
    data length hcd hhead hlen hdata
  let tail := (data.extract 0 length.toNat) ++ ByteArray.zeroes (ABI.paddedSize length.toNat - length.toNat)
  have htail : tail.size = ABI.paddedSize length.toNat := by
    dsimp only [tail]
    rw [ByteArray.size_append, hbytes, ByteArray_zeroes_size]
    omega
  have hload : memLoad ⟨96⟩ (((front ++ (UInt256.ofNat 32).toByteArray) ++ length.toByteArray) ++ tail) = length := by
    have h := memLoad_append_word (front ++ (UInt256.ofNat 32).toByteArray) tail length
      (by rw [hhead]; decide +kernel)
    rw [hhead] at h
    exact h
  have hpadded' : vaultStringPaddedMem I (((front ++ (UInt256.ofNat 32).toByteArray) ++ length.toByteArray) ++ data) =
      ((front ++ (UInt256.ofNat 32).toByteArray) ++ length.toByteArray) ++ tail := by
    rw [hpadded, ByteArray.append_assoc]
  have hsize : (((front ++ (UInt256.ofNat 32).toByteArray) ++ length.toByteArray) ++ tail).size =
      128 + ABI.paddedSize length.toNat := by
    rw [ByteArray.size_append, ByteArray.size_append, hhead, toByteArray_size, htail]
  unfold vaultStringOutput
  rw [hpadded', hload, vyperStringOutputSize length hlen,
    readWithPadding_eq_extract_unbounded _ 64 _ (by omega) (by rw [hsize]; omega)]
  rw [ByteArray.append_assoc, ByteArray.append_assoc,
    extract_append_right_window front _ _ _ (by omega), hfront]
  rw [show 64 - 64 = 0 by omega, show 64 + (64 + ABI.paddedSize length.toNat) - 64 =
    64 + ABI.paddedSize length.toNat by omega]
  have hrest : (((UInt256.ofNat 32).toByteArray ++ length.toByteArray) ++ tail).size =
      64 + ABI.paddedSize length.toNat := by
    rw [ByteArray.size_append, ByteArray.size_append, toByteArray_size, toByteArray_size, htail]
  rw [← ByteArray.append_assoc, ← hrest, byteArray_extract_self,
    stringReturnEncoding, hbytes, u256_ofNat_toNat]
  simp only [tail, ByteArray.append_assoc]

end Benchmarks.CurveVault
