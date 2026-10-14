import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultClear

/-! The constructor loads metadata event topics from code while restoring scratch memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

-- LIBRARY CANDIDATE: saving and restoring scratch word zero cancels a temporary code copy.
theorem writeWord_restore_copy32 (src mem : ByteArray) (off : Nat)
    (hsrc : off + 32 ≤ src.size) (hmem : 32 ≤ mem.size) :
    writeWord (src.write off mem 0 32) 0 (memLoad ⟨0⟩ mem) = mem := by
  have hw : (memLoad ⟨0⟩ mem).toByteArray = mem.extract 0 32 := by
    rw [memLoad, if_neg (by change ¬ 0 ≥ mem.size; omega)]
    rw [← uInt256OfByteArray_eq]
    change (uInt256OfByteArray (mem.readWithPadding 0 32)).toByteArray = _
    rw [← read32_roundtrip mem 0 hmem, readWithPadding_eq_extract mem 0 hmem]
  have hcopy : src.write off mem 0 32 =
      src.extract off (off + 32) ++ mem.extract 32 mem.size := by
    rw [write_eq_gen_from src mem off 0 32 (by decide) hsrc hmem]
    simp only [show mem.extract 0 0 = ByteArray.empty from by simp,
      ByteArray.empty_append, Nat.zero_add]
  have hs : (src.extract off (off + 32)).size = 32 := by rw [ByteArray.size_extract]; omega
  have ht : (mem.extract 32 mem.size).size = mem.size - 32 := by rw [ByteArray.size_extract]; omega
  rw [Reasoning.Theory.writeWord, hw, write_eq_gen_from _ _ 0 0 32 (by decide)
    (by rw [ByteArray.size_extract]; omega)
    (by rw [hcopy, ByteArray.size_append, hs, ht]; omega)]
  simp only [show (src.write off mem 0 32).extract 0 0 = ByteArray.empty from by simp,
    ByteArray.empty_append, Nat.zero_add]
  rw [extract_extract_BA, show min (0 + 32) 32 = 32 by decide]
  rw [hcopy, ByteArray.size_append, hs, ht,
    show 32 + (mem.size - 32) = mem.size by omega,
    extract_append_right_window _ _ _ _ (by rw [hs]), hs, extract_extract_BA]
  simp only [Nat.sub_self, Nat.add_zero]
  rw [show min (32 + (mem.size - 32)) mem.size = mem.size by omega,
    ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
    Nat.max_eq_right hmem, ByteArray.extract_zero_size]

def constructorVaultTopicOffset (symbol : Bool) : Nat := if symbol then 23634 else 23602

theorem constructorVaultTopicRead (tail mem : ByteArray) (symbol : Bool) :
    memLoad ⟨0⟩ ((metaMorphoV1_1CreationBytecode ++ tail).write
      (constructorVaultTopicOffset symbol) mem 0 32) = stringSetTopic symbol := by
  have hs : constructorVaultTopicOffset symbol + 32 ≤ metaMorphoV1_1CreationBytecode.size := by
    rw [metaMorphoV1_1CreationBytecode_size]
    cases symbol <;> decide
  apply loadedWord_of_read
  · change 0 + 32 ≤ _
    exact write0_from_size_ge_len _ _ _ _ (by decide)
      (by rw [ByteArray.size_append]; omega)
  · change ((metaMorphoV1_1CreationBytecode ++ tail).write
        (constructorVaultTopicOffset symbol) mem 0 32).readWithPadding 0 32 = _
    rw [write0_read_back_from_gen _ _ _ _ (by decide)
      (by rw [ByteArray.size_append]; omega) (by decide),
      extract_append_left _ _ _ _ hs]
    cases symbol <;> native_decide

theorem constructorVaultTopicRestore (tail mem : ByteArray) (symbol : Bool)
    (hmem : 32 ≤ mem.size) :
    writeWord ((metaMorphoV1_1CreationBytecode ++ tail).write
      (constructorVaultTopicOffset symbol) mem 0 32) 0 (memLoad ⟨0⟩ mem) = mem := by
  apply writeWord_restore_copy32 _ _ _ _ hmem
  rw [ByteArray.size_append, metaMorphoV1_1CreationBytecode_size]
  cases symbol <;> simp [constructorVaultTopicOffset] <;> omega

end Benchmarks.Morpho.MetaMorphoV1_1
