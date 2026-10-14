import Benchmarks.EAS.EAS.CopyEncodeViews
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: the low bytes of a word encode its natural-value remainder.
theorem bytesBE_drop_word (w : UInt256) (n : Nat) :
    fromBytesBigEndian ((EVM.Word.toBytesBE w).drop n) = w.toNat % 256^(32-n) := by
  have hbe : EVM.Word.toBytesBE w = (EVM.Word.toBytesLEWithSizeProof w).1.reverse := by
    simp only [EVM.Word.toBytesBE,EVM.Word.toBytesLEWithSizeProof,List.reverse_append,List.reverse_replicate,toBytesBigEndian,Function.comp_apply,List.length_reverse]
  rw [hbe]
  change fromBytes' (((EVM.Word.toBytesLEWithSizeProof w).1.reverse).drop n).reverse = _
  rw [List.reverse_drop,List.reverse_reverse]
  have hl : (EVM.Word.toBytesLEWithSizeProof w).1.length = 32 := (EVM.Word.toBytesLEWithSizeProof w).2
  rw [List.length_reverse,hl]
  exact fromBytes'_take_wordLE w (32-n)


-- LIBRARY CANDIDATE: shifting by whole bytes moves the low word bytes into the prefix.
theorem shiftLeft_bytes_prefix (w : UInt256) (n : Nat) (hn : n < 32) :
    ((UInt256.shiftLeft w (UInt256.ofNat (8*n))).toByteArray.extract 0 (32-n)).toList =
      (EVM.Word.toBytesBE w).drop n := by
  apply fromBytesBigEndian_inj_of_length
  · rw [byteArray_toList_eq,Array.length_toList]
    change ((UInt256.shiftLeft w (UInt256.ofNat (8*n))).toByteArray.extract 0 (32-n)).size = _
    rw [ByteArray.size_extract,toByteArray_size,List.length_drop,word_toBytesBE_length_32]
    omega
  · rw [bytesBE_extract_high _ _ (by omega),bytesBE_drop_word]
    have hnword : (UInt256.ofNat (8*n)).toNat = 8*n := ulit_toNat' _ (by change 8*n < 2^256; omega)
    have hshift : (UInt256.shiftLeft w (UInt256.ofNat (8*n))).toNat = (w.toNat*2^(8*n))%UInt256.size := by
      unfold UInt256.shiftLeft
      rw [if_neg (by change ¬ (UInt256.ofNat (8*n)).toNat ≥ 256; rw [hnword]; omega)]
      change (w.toNat <<< (UInt256.ofNat (8*n)).toNat)%UInt256.size = _
      rw [hnword,Nat.shiftLeft_eq]
    have hmod : UInt256.size = 2^(8*(32-n))*2^(8*n) := by
      rw [← Nat.pow_add]
      change 2^256 = 2^(8*(32-n)+8*n)
      congr 1
      omega
    rw [hshift,show 32-(32-n)=n by omega,hmod,Nat.mul_mod_mul_right,Nat.mul_div_cancel _ (by positivity)]
    rw [show (256 : Nat)=2^8 by decide,← Nat.pow_mul]

end Benchmarks.EAS.EAS
