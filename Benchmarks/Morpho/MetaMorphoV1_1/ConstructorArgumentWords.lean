import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorArgumentMemory

/-! Reading the scalar head and string lengths from copied constructor arguments. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- GENERALIZES Reasoning.Theory.natBytes_read1 to a word after an arbitrary encoded prefix.
theorem encodedWord_read (init rest : List UInt8) (word : UInt256) :
    (init ++ EVM.Word.toBytesBE word ++ rest).toByteArray.readWithPadding init.length 32 =
      word.toByteArray := by
  rw [List.toByteArray_append, List.toByteArray_append,
    readWithPadding_eq_extract _ _ (by
      simp only [ByteArray.size_append, List.size_toByteArray, word_toBytesBE_length_32]
      omega),
    extract_append_left _ _ _ _ (by
      simp only [ByteArray.size_append, List.size_toByteArray, word_toBytesBE_length_32]
      omega),
    extract_append_right_window _ _ _ _ (by rw [List.size_toByteArray]),
    List.size_toByteArray, Nat.sub_self, Nat.add_sub_cancel_left,
    word_toBytesBE_toByteArray_eq_toByteArray, toByteArray_extract_all]

namespace ConstructorArgs

def headWords (a : ConstructorArgs) : List UInt256 :=
  [UInt256.ofNat a.owner.val, UInt256.ofNat a.morpho.val, a.initialTimelock,
   UInt256.ofNat a.asset.val, UInt256.ofNat 192,
   UInt256.ofNat (224 + paddedSize a.name.size)]

def headWord (a : ConstructorArgs) (i : Fin 6) : UInt256 := a.headWords[i.val]'i.isLt

end ConstructorArgs

-- LIBRARY CANDIDATE: byte length of an encoded sequence of EVM words.
theorem encodedWords_length (words : List UInt256) :
    (words.flatMap EVM.Word.toBytesBE).length = 32 * words.length := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [List.flatMap_cons, List.length_append, word_toBytesBE_length_32,
      ih, List.length_cons, Nat.mul_succ]
    omega

-- LIBRARY CANDIDATE: read any complete encoded word, independently of following dynamic tails.
theorem encodedWords_read (words : List UInt256) (rest : List UInt8) (i : Nat)
    (hi : i < words.length) :
    (words.flatMap EVM.Word.toBytesBE ++ rest).toByteArray.readWithPadding (32 * i) 32 =
      words[i].toByteArray := by
  have hsplit : words.take i ++ [words[i]] ++ words.drop (i + 1) = words := by
    rw [List.take_append_getElem hi]
    exact List.take_append_drop _ _
  have hbytes : words.flatMap EVM.Word.toBytesBE ++ rest =
      (words.take i).flatMap EVM.Word.toBytesBE ++ EVM.Word.toBytesBE words[i] ++
        ((words.drop (i + 1)).flatMap EVM.Word.toBytesBE ++ rest) := by
    conv_lhs => rw [← hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc]
  have hlen : ((words.take i).flatMap EVM.Word.toBytesBE).length = 32 * i := by
    rw [encodedWords_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [hbytes, ← hlen]
  exact encodedWord_read _ _ _

namespace ConstructorArgs

theorem encoded_head (a : ConstructorArgs) :
    a.encoded = a.headWords.flatMap EVM.Word.toBytesBE ++
      (natBytes a.name.size ++ padRightToWord a.name.toList ++
        natBytes a.symbol.size ++ padRightToWord a.symbol.toList) := by
  simp only [encoded, headWords, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc, natBytes, EVM.Word.ofNat]

theorem encoded_headWord (a : ConstructorArgs) (i : Fin 6) :
    a.encoded.toByteArray.readWithPadding (32 * i.val) 32 = (a.headWord i).toByteArray := by
  rw [encoded_head]
  exact encodedWords_read _ _ _ i.isLt

theorem encoded_nameLength (a : ConstructorArgs) :
    a.encoded.toByteArray.readWithPadding 192 32 =
      (UInt256.ofNat a.name.size).toByteArray := by
  have h := encodedWord_read (a.headWords.flatMap EVM.Word.toBytesBE)
    (padRightToWord a.name.toList ++ natBytes a.symbol.size ++ padRightToWord a.symbol.toList)
    (UInt256.ofNat a.name.size)
  rw [encodedWords_length] at h
  simpa only [encoded_head, headWords, List.length_cons, List.length_nil,
    natBytes, EVM.Word.ofNat, List.append_assoc] using h

theorem encoded_symbolLength (a : ConstructorArgs) :
    a.encoded.toByteArray.readWithPadding (224 + paddedSize a.name.size) 32 =
      (UInt256.ofNat a.symbol.size).toByteArray := by
  have h := encodedWord_read
    (a.headWords.flatMap EVM.Word.toBytesBE ++ natBytes a.name.size ++ padRightToWord a.name.toList)
    (padRightToWord a.symbol.toList) (UInt256.ofNat a.symbol.size)
  have hlen :
      (a.headWords.flatMap EVM.Word.toBytesBE ++ natBytes a.name.size ++
        padRightToWord a.name.toList).length = 224 + paddedSize a.name.size := by
    simp only [List.length_append, encodedWords_length, headWords, List.length_cons,
      List.length_nil, natBytes, word_toBytesBE_length_32, abiPaddedBytes_length]
  rw [hlen] at h
  simpa only [encoded_head, natBytes, EVM.Word.ofNat, List.append_assoc] using h

end ConstructorArgs

theorem constructorArgumentMemory_headWord (a : ConstructorArgs) (i : Fin 6) :
    memLoad (UInt256.ofNat (480 + 32 * i.val)) (constructorArgumentMemory a) =
      a.headWord i := by
  have hoff : 480 + 32 * i.val < UInt256.size := by
    have := i.isLt
    have : 640 < UInt256.size := by decide
    omega
  have hin : 32 * i.val + 32 ≤ a.encoded.length := by
    have := i.isLt
    rw [a.encoded_length]
    omega
  apply loadedWord_of_read
  · rw [UInt256.toNat_ofNat_of_lt hoff, constructorArgumentMemory_size]
    omega
  · rw [UInt256.toNat_ofNat_of_lt hoff, constructorArgumentMemory_readWord a _ hin]
    exact a.encoded_headWord i

end Benchmarks.Morpho.MetaMorphoV1_1
