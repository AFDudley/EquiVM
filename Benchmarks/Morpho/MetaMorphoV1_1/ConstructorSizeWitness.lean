import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorEncoding

/-! A symbolic constructor-encoding collision at the EVM size-word boundary.

This file checks the input-domain issue without changing the refinement statement or
deployment encoder. It does not claim a complete counterexample to constructor refinement.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.ConstructorSizeWitness

set_option maxRecDepth 2000
attribute [local irreducible] metaMorphoV1_1CreationBytecode

def nameBytes (n : Nat) : ByteArray := (List.replicate n (0 : UInt8)).toByteArray

def arguments (n : Nat) : List Value :=
  [.address (AccountAddress.ofNat 1), .address (AccountAddress.ofNat 2), .int 0,
   .address (AccountAddress.ofNat 3), .bytes (nameBytes n), .bytes ByteArray.empty]

def headBytes (n : Nat) : List UInt8 :=
  natBytes 1 ++ natBytes 2 ++ natBytes 0 ++ natBytes 3 ++ natBytes 192 ++ natBytes (224 + n)

def encodedArgs (n : Nat) : List UInt8 :=
  headBytes n ++ natBytes n ++ List.replicate n 0 ++ natBytes 0

theorem arguments_encoded (n : Nat) (hn : paddedSize n = n) :
    encodeABIValues? (contract.ctor.params.map Param.ty) (arguments n) = some (encodedArgs n) := by
  have hbytes : (nameBytes n).size = n := by simp only [nameBytes, List.size_toByteArray, List.length_replicate]
  have hlist : (nameBytes n).toList = List.replicate n 0 := by
    simp only [nameBytes, byteArray_toList_eq, List.toList_data_toByteArray]
  have hnat (m : Nat) : (natBytes m).length = 32 := word_toBytesBE_length_32 _
  change encodeABIValues?
    [.elem .address, .elem .address, .elem (.int (.uint ⟨256, by decide⟩)),
      .elem .address, .string, .string] (arguments n) = _
  simp only [arguments, encodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
    staticABIEncodedSize?, encodeABIValuesFrom?, encodeABIValue?, encodeABIWord?,
    show (256 : Nat) ≠ 0 from by decide, show (0 : Int) ≤ 0 ∧ 0 < Int.ofNat (EVM.twoPow 256) from by decide,
    Bool.false_eq_true, and_self, if_false, if_true,
    bind, Option.bind, pure, hbytes, hlist, List.length_replicate, hn, padRightToWord,
    zeroBytes, List.length_append, hnat, List.length_nil, Nat.sub_self,
    List.replicate_zero, List.append_nil, List.nil_append, Nat.add_zero,
    ByteArray.size_empty, ByteArray.toList_empty]
  simp only [show paddedSize 0 = 0 from by decide, Nat.sub_self, List.replicate_zero, List.append_nil]
  change some ((natBytes 1 ++ natBytes 2 ++ natBytes 0 ++ natBytes 3 ++ natBytes 192 ++
    natBytes (192 + (32 + n))) ++ (natBytes n ++ List.replicate n 0 ++ natBytes 0)) = _
  simp only [encodedArgs, headBytes, List.append_assoc, ← Nat.add_assoc]

theorem deployment (n : Nat) (hn : paddedSize n = n) :
    config.selfDeployment metaMorphoV1_1CreationBytecode (arguments n) =
      some (metaMorphoV1_1CreationBytecode ++ (encodedArgs n).toByteArray) := by
  change (do
    let bytes ← encodeABIValues? (contract.ctor.params.map Param.ty) (arguments n)
    pure (metaMorphoV1_1CreationBytecode ++ bytes.toByteArray)) = _
  rw [arguments_encoded n hn]
  rfl

theorem headBytes_length (n : Nat) : (headBytes n).length = 192 := by
  simp only [headBytes, List.length_append, natBytes, word_toBytesBE_length_32]

theorem encodedArgs_length (n : Nat) : (encodedArgs n).length = 256 + n := by
  simp only [encodedArgs, List.length_append, headBytes_length, natBytes,
    word_toBytesBE_length_32, List.length_replicate]
  omega

theorem encodedLength_wraps : natBytes UInt256.size = natBytes 0 := by
  apply congrArg EVM.Word.toBytesBE
  decide

theorem encodedOffset_wraps : natBytes (224 + UInt256.size) = natBytes 224 := by
  apply congrArg EVM.Word.toBytesBE
  decide

theorem encodedHead_wraps : headBytes UInt256.size = headBytes 0 := by
  simp only [headBytes, encodedOffset_wraps, Nat.add_zero]

theorem encodedPrefix_wraps : (encodedArgs UInt256.size).take 256 = encodedArgs 0 := by
  have htake : 256 = (headBytes UInt256.size ++ natBytes UInt256.size).length + 32 := by
    rw [List.length_append, headBytes_length, show (natBytes UInt256.size).length = 32 from
      word_toBytesBE_length_32 _]
  unfold encodedArgs
  rw [List.append_assoc (headBytes UInt256.size ++ natBytes UInt256.size)
    (List.replicate UInt256.size 0) (natBytes 0), htake, List.take_length_add_append]
  rw [List.take_append_of_le_length
    (l₁ := List.replicate UInt256.size (0 : UInt8))
    (by rw [List.length_replicate]; decide)]
  rw [List.take_replicate]
  have hmin : min 32 UInt256.size = 32 := by decide
  rw [hmin, encodedHead_wraps]
  change headBytes 0 ++ natBytes UInt256.size ++ List.replicate 32 0 = encodedArgs 0
  rw [encodedLength_wraps, show List.replicate 32 (0 : UInt8) = natBytes 0 from by native_decide]
  simp only [encodedArgs, List.replicate_zero, List.append_nil]

theorem codesize_word (init : ByteArray) (n : Nat) :
    UInt256.ofNat (init ++ (encodedArgs n).toByteArray).size =
      UInt256.ofNat (init.size + 256 + n) := by
  apply congrArg UInt256.ofNat
  rw [ByteArray.size_append, List.size_toByteArray, encodedArgs_length, Nat.add_assoc]

-- LIBRARY CANDIDATE: word equality from equality of the residues, without reducing large arguments.
theorem wordOfNat_eq_of_mod (a b : Nat) (h : a % UInt256.size = b % UInt256.size) :
    UInt256.ofNat a = UInt256.ofNat b := u256_inj h

theorem codesize_wraps (init : ByteArray) :
    UInt256.ofNat (init ++ (encodedArgs UInt256.size).toByteArray).size =
      UInt256.ofNat (init ++ (encodedArgs 0).toByteArray).size := by
  have hmod : UInt256.ofNat (init.size + 256 + UInt256.size) =
      UInt256.ofNat (init.size + 256 + 0) :=
    wordOfNat_eq_of_mod _ _ (Nat.add_mod_right _ _)
  exact (codesize_word init UInt256.size).trans (hmod.trans (codesize_word init 0).symm)

theorem sourceName_differs : nameBytes UInt256.size ≠ nameBytes 0 := by
  intro h
  have hh := congrArg ByteArray.size h
  simp only [nameBytes, List.size_toByteArray, List.length_replicate] at hh
  exact (by decide : UInt256.size ≠ 0) hh

theorem sourceStorageHeader_differs :
    solidityBytesHeaderWord UInt256.size = ⟨1⟩ ∧ solidityBytesHeaderWord 0 = ⟨0⟩ := by
  decide

theorem admittedInput_wraps :
    config.selfDeployment metaMorphoV1_1CreationBytecode (arguments UInt256.size) =
        some (metaMorphoV1_1CreationBytecode ++ (encodedArgs UInt256.size).toByteArray) ∧
      UInt256.size ≤
        (metaMorphoV1_1CreationBytecode ++ (encodedArgs UInt256.size).toByteArray).size ∧
      (encodedArgs UInt256.size).take 256 = encodedArgs 0 ∧
      UInt256.ofNat (metaMorphoV1_1CreationBytecode ++ (encodedArgs UInt256.size).toByteArray).size =
        UInt256.ofNat (metaMorphoV1_1CreationBytecode ++ (encodedArgs 0).toByteArray).size ∧
      nameBytes UInt256.size ≠ nameBytes 0 := by
  refine ⟨deployment _ (by decide), ?_, encodedPrefix_wraps, codesize_wraps _, sourceName_differs⟩
  rw [ByteArray.size_append, List.size_toByteArray, encodedArgs_length]
  omega

theorem deployment_doesNotImplyCodeBound :
    ¬ (∀ (args : List Value) (code : ByteArray),
      config.selfDeployment metaMorphoV1_1CreationBytecode args = some code →
        code.size < UInt256.size) := by
  intro hbound
  exact Nat.not_lt.mpr admittedInput_wraps.2.1
    (hbound _ _ admittedInput_wraps.1)

theorem creationCode_size : metaMorphoV1_1CreationBytecode.size = 23666 :=
  metaMorphoV1_1CreationBytecode_size

/-- The constructor's actual CODESIZE subtraction requests only 256 argument bytes. -/
theorem copiedLength_wraps :
    UInt256.sub
      (UInt256.ofNat (metaMorphoV1_1CreationBytecode ++ (encodedArgs UInt256.size).toByteArray).size)
      (UInt256.ofNat 23666) = UInt256.ofNat 256 := by
  rw [codesize_wraps, codesize_word, creationCode_size]
  decide

/-- The requested argument window is exactly the ordinary empty-name encoding. -/
theorem copiedArgumentWindow (init : ByteArray) :
    (init ++ (encodedArgs UInt256.size).toByteArray).extract init.size (init.size + 256) =
      (encodedArgs 0).toByteArray := by
  rw [extract_append_right_window _ _ _ _ (le_refl _), Nat.sub_self, Nat.add_sub_cancel_left]
  apply byteArray_eq_of_toList_eq
  rw [byteArray_extract_toList]
  simp only [byteArray_toList_eq, List.toList_data_toByteArray, Nat.sub_zero, List.drop_zero]
  exact encodedPrefix_wraps

end Benchmarks.Morpho.MetaMorphoV1_1.ConstructorSizeWitness
