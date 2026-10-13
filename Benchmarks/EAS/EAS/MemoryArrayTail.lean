import Benchmarks.EAS.EAS.SignatureArrayDecode
import Benchmarks.EAS.EAS.RevocationArrayDecode
import Benchmarks.EAS.EAS.ReferenceTail
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def arrayHeaderReadable (cd : ByteArray) (header : UInt256) : Prop :=
  UInt256.isZero (UInt256.slt (header+UInt256.ofNat 31) (UInt256.ofNat cd.size)) = ⟨0⟩
instance (cd : ByteArray) (header : UInt256) : Decidable (arrayHeaderReadable cd header) :=
  inferInstanceAs (Decidable (_ = _))

-- LIBRARY CANDIDATE: memory array decoding adds the length-word bound at a direct tail.
theorem memoryArray_tail (ty : ABIType) (cd : ByteArray) (header : UInt256) :
    decodeValue? (.dynamicArray ty) cd.toList header.toNat {} false =
      if arrayHeaderReadable cd header then decodeValue? (.dynamicArray ty) cd.toList header.toNat {} true else none := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  have h31 : solcAdd header.toNat 31 = (header+UInt256.ofNat 31).toNat := solcAdd_word header (UInt256.ofNat 31)
  have hmod : solcSLT (header+UInt256.ofNat 31).toNat cd.size =
      solcSLT (header+UInt256.ofNat 31).toNat (UInt256.ofNat cd.size).toNat := by
    unfold solcSLT
    simp only [EVM.Word.ofNat,u256_ofNat_toNat]
  by_cases hh : arrayHeaderReadable cd header
  · have hs := (solcSLT_word_true (header+UInt256.ofNat 31) (UInt256.ofNat cd.size)).mpr hh
    rw [if_pos hh,decodeValue?,decodeValue?]
    simp only [isMemory,show ({} : CalldataPlan).materialize = [[]] from rfl,List.contains_cons,List.contains_nil,
      beq_self_eq_true,Bool.true_or,badExtent,Bool.not_false,Bool.not_true,Bool.true_and,Bool.false_and,
      Bool.and_false,Bool.false_eq_true,if_false,hlen,h31,hmod,hs,Bool.false_or]
  · have hs : solcSLT (header+UInt256.ofNat 31).toNat (UInt256.ofNat cd.size).toNat = false := by
      cases h : solcSLT (header+UInt256.ofNat 31).toNat (UInt256.ofNat cd.size).toNat
      · rfl
      · exact False.elim (hh ((solcSLT_word_true _ _).mp h))
    rw [if_neg hh,decodeValue?]
    simp only [isMemory,show ({} : CalldataPlan).materialize = [[]] from rfl,List.contains_cons,List.contains_nil,
      beq_self_eq_true,Bool.true_or,badExtent,Bool.not_false,Bool.not_true,Bool.true_and,Bool.false_and,
      Bool.and_false,Bool.false_eq_true,if_false,hlen,h31,hmod,hs,Bool.true_or,Bool.or_true]
    cases stride? ty <;> rfl

end Benchmarks.EAS.EAS
