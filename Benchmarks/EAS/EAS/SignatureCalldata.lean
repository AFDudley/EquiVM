import Benchmarks.EAS.EAS.SignatureDecode
import Benchmarks.EAS.EAS.CalldataGuards
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def signatureAt (cd : ByteArray) (ptr : UInt256) : SignatureRecord :=
  ⟨calldataWord cd ptr.toNat,calldataWord cd (ptr+UInt256.ofNat 32).toNat,
    calldataWord cd (ptr+UInt256.ofNat 64).toNat⟩

theorem decodeSignatureWordBytes (s : SignatureRecord) :
    decodeABIValue? signatureABI (EVM.Word.toBytesBE s.v ++ EVM.Word.toBytesBE s.r ++ EVM.Word.toBytesBE s.s) 0 =
      if signatureClean s then some (s.tuple,96) else none := by
  have ht (w : UInt256) : (EVM.Word.toBytesBE w).take 32 = EVM.Word.toBytesBE w :=
    List.take_of_length_le (by rw [word_toBytesBE_length_32])
  have hd (w : UInt256) : (EVM.Word.toBytesBE w).drop 32 = [] :=
    List.drop_of_length_le (by rw [word_toBytesBE_length_32])
  have hd64 (w : UInt256) : (EVM.Word.toBytesBE w).drop 64 = [] :=
    List.drop_of_length_le (by rw [word_toBytesBE_length_32]; decide)
  have slices := decodeSignatureTuple (bytes := EVM.Word.toBytesBE s.v ++ EVM.Word.toBytesBE s.r ++ EVM.Word.toBytesBE s.s)
    (start := 0)
    (by simp only [List.length_take,List.length_drop,List.length_append,word_toBytesBE_length_32]; decide)
    (by simp only [List.length_take,List.length_drop,List.length_append,word_toBytesBE_length_32]; decide)
    (by simp only [List.length_take,List.length_drop,List.length_append,word_toBytesBE_length_32]; decide)
  rw [slices]
  simp only [List.drop_zero,List.drop_append,List.take_append,List.length_append,word_toBytesBE_length_32,
    ht,hd,hd64,Nat.reduceAdd,Nat.reduceSub,List.take_zero,List.nil_append,List.append_nil,bytesToWord_toBytesBE]
  rw [show abiUInt8 = .elem (.int (.uint ⟨8,by decide⟩)) from rfl,
    decodeUIntWord_mask ⟨8,by decide⟩ s.v (UInt256.ofNat 255) rfl (by decide)]
  by_cases hc : signatureClean s
  · rw [if_pos hc,if_pos (show s.v = UInt256.land s.v (UInt256.ofNat 255) from hc)]
    rfl
  · rw [if_neg hc,if_neg (show ¬ s.v = UInt256.land s.v (UInt256.ofNat 255) from hc)]
    rfl

theorem signatureAt_words (cd : ByteArray) (ptr : UInt256) :
    solcReadWords cd.toList ptr.toNat 3 = EVM.Word.toBytesBE (signatureAt cd ptr).v ++
      EVM.Word.toBytesBE (signatureAt cd ptr).r ++ EVM.Word.toBytesBE (signatureAt cd ptr).s := by
  have h0 : solcAdd ptr.toNat 0 = ptr.toNat := Nat.mod_eq_of_lt ptr.val.isLt
  have h32 : solcAdd ptr.toNat 32 = (ptr+UInt256.ofNat 32).toNat := solcAdd_word ptr (UInt256.ofNat 32)
  have h64 : solcAdd ptr.toNat 64 = (ptr+UInt256.ofNat 64).toNat := solcAdd_word ptr (UInt256.ofNat 64)
  simp only [solcReadWords,List.range_succ,List.range_zero,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.nil_append,Nat.reduceMul,h0,h32,h64,solcReadBytes_word_total]
  rfl

theorem signatureAt_decode (cd : ByteArray) (ptr : UInt256) (tailAccess : Bool)
    (hhead : UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) ptr) ⟨96⟩ = ⟨0⟩) :
    decodeValue? signatureABI cd.toList ptr.toNat {} tailAccess =
      if signatureClean (signatureAt cd ptr) then some (signatureAt cd ptr).tuple else none := by
  have hl : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  have hs : solcSub cd.size ptr.toNat = (UInt256.sub (UInt256.ofNat cd.size) ptr).toNat := by
    unfold solcSub EVM.Word.ofNat
    rw [u256_ofNat_toNat]
    rfl
  have hcheck : solcSLT (UInt256.sub (UInt256.ofNat cd.size) ptr).toNat 96 = false :=
    (solcSLT_word_false _ (⟨96⟩ : UInt256)).mpr hhead
  rw [signatureABI,decodeValue?]
  simp only [show abiTupleHeadSize? [abiUInt8,abiBytes32,abiBytes32] = some 96 by native_decide,
    show isDynamicABIType (.tuple [abiUInt8,abiBytes32,abiBytes32]) = false from rfl,
    show isMemory ({} : CalldataPlan) = true from rfl,
    Bool.or_true,Bool.true_and,Bool.not_false,bind,Option.bind_some,hl,hs,
    hcheck,Bool.false_eq_true,if_false,if_true]
  rw [show 96/32 = 3 from rfl,signatureAt_words,← signatureABI,decodeSignatureWordBytes]
  by_cases hc : signatureClean (signatureAt cd ptr) <;> simp only [hc,if_true,if_false,Option.map_some,Option.map_none]


def signatureAtValid (cd : ByteArray) (ptr : UInt256) : Prop :=
  UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) ptr) ⟨96⟩ = ⟨0⟩ ∧ signatureClean (signatureAt cd ptr)
instance (cd : ByteArray) (ptr : UInt256) : Decidable (signatureAtValid cd ptr) := inferInstanceAs (Decidable (_ ∧ _))

theorem signatureAt_decode_cases (cd : ByteArray) (ptr : UInt256) (tailAccess : Bool) :
    decodeValue? signatureABI cd.toList ptr.toNat {} tailAccess =
      if signatureAtValid cd ptr then some (signatureAt cd ptr).tuple else none := by
  by_cases hh : UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) ptr) ⟨96⟩ = ⟨0⟩
  · rw [signatureAt_decode cd ptr tailAccess hh]
    simp only [signatureAtValid,hh,true_and]
  · have hcheck : solcSLT (UInt256.sub (UInt256.ofNat cd.size) ptr).toNat 96 = true := by
      cases hc : solcSLT (UInt256.sub (UInt256.ofNat cd.size) ptr).toNat 96
      · exact False.elim (hh ((solcSLT_word_false _ (⟨96⟩ : UInt256)).mp hc))
      · rfl
    have hl : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
    have hs : solcSub cd.size ptr.toNat = (UInt256.sub (UInt256.ofNat cd.size) ptr).toNat := by
      unfold solcSub EVM.Word.ofNat
      rw [u256_ofNat_toNat]
      rfl
    rw [signatureABI,decodeValue?]
    simp only [show abiTupleHeadSize? [abiUInt8,abiBytes32,abiBytes32] = some 96 by native_decide,
      show isMemory ({} : CalldataPlan) = true from rfl,Bool.or_true,Bool.true_and,
      bind,Option.bind_some,hl,hs,hcheck,if_true]
    rw [if_neg (fun h => hh h.1)]

end Benchmarks.EAS.EAS
