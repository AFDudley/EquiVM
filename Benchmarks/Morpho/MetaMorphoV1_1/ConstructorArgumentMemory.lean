import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorEntry

/-! Exact memory after the initial copy of the encoded constructor arguments. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

namespace SourceMemory

-- LIBRARY CANDIDATE: the Solidity allocator leaves an aligned, non-wrapping size unchanged.
theorem roundedSize_aligned {n : Nat} (halign : n % 32 = 0)
    (hsize : n + 31 < UInt256.size) :
    roundedSize (UInt256.ofNat n) = UInt256.ofNat n := by
  apply u256_inj
  rw [roundedSize_toNat, UInt256.toNat_ofNat_of_lt (by omega),
    Nat.mod_eq_of_lt hsize, nat_ceil32_eq_div_of_mod_zero halign]
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero halign)

theorem constructorFirstAllocation_iff (a : ConstructorArgs)
    (hbound : 23666 + a.encoded.length < UInt256.size) :
    allocationFits ⟨480⟩ (UInt256.ofNat a.encoded.length) ↔
      480 + a.encoded.length < 2 ^ 64 := by
  rw [allocationFits_iff_sum_lt,
    roundedSize_aligned a.encoded_length_mod (by omega),
    UInt256.toNat_ofNat_of_lt (by omega)]
  rfl

theorem constructorFirstCursor (a : ConstructorArgs)
    (hbound : 23666 + a.encoded.length < UInt256.size) :
    nextCursor ⟨480⟩ (UInt256.ofNat a.encoded.length) =
      UInt256.ofNat (480 + a.encoded.length) := by
  rw [nextCursor, roundedSize_aligned a.encoded_length_mod (by omega)]
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega),
    UInt256.toNat_ofNat_of_lt (by omega)]
  exact Nat.mod_eq_of_lt (by change 480 + a.encoded.length < UInt256.size; omega)

end SourceMemory

def constructorAllocatedMemory (a : ConstructorArgs) : ByteArray :=
  writeWord constructorInitialMemory 64 (UInt256.ofNat (480 + a.encoded.length))

def constructorArgumentMemory (a : ConstructorArgs) : ByteArray :=
  (constructorAllocatedMemory a ++ ByteArray.zeroes 384) ++ a.encoded.toByteArray

theorem constructorAllocatedMemory_size (a : ConstructorArgs) :
    (constructorAllocatedMemory a).size = 96 := by
  simp only [constructorAllocatedMemory, constructorInitialMemory, writeWord_sparse_size,
    ByteArray.size_empty]
  rfl

theorem constructorArgumentMemory_size (a : ConstructorArgs) :
    (constructorArgumentMemory a).size = 480 + a.encoded.length := by
  rw [constructorArgumentMemory, ByteArray.size_append, ByteArray.size_append,
    constructorAllocatedMemory_size, ByteArray_zeroes_size, List.size_toByteArray]

theorem constructorCopyArguments (a : ConstructorArgs) :
    (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray).write
      23666 (constructorAllocatedMemory a) 480 a.encoded.length =
      constructorArgumentMemory a := by
  have hpos : a.encoded.length ≠ 0 := by rw [a.encoded_length]; omega
  rw [write_from_gap_eq' _ _ _ _ _ hpos
    (by rw [ByteArray.size_append, metaMorphoV1_1CreationBytecode_size,
      List.size_toByteArray])
    (by rw [constructorAllocatedMemory_size]; decide)
    (by rw [constructorAllocatedMemory_size]; exact lt_usize _ (by decide))]
  rw [constructorAllocatedMemory_size]
  have hextract := extract_append_right metaMorphoV1_1CreationBytecode a.encoded.toByteArray
  rw [metaMorphoV1_1CreationBytecode_size, List.size_toByteArray] at hextract
  rw [hextract]
  rfl

set_option maxRecDepth 2000 in
theorem constructorArgumentMemory_extract (a : ConstructorArgs) (off len : Nat) :
    (constructorArgumentMemory a).extract (480 + off) (480 + off + len) =
      a.encoded.toByteArray.extract off (off + len) := by
  have hp : (constructorAllocatedMemory a ++ ByteArray.zeroes 384).size = 480 := by
    rw [ByteArray.size_append, constructorAllocatedMemory_size, ByteArray_zeroes_size]
  rw [constructorArgumentMemory, extract_append_right_window _ _ _ _ (by rw [hp]; omega), hp]
  congr 1 <;> omega

theorem constructorArgumentMemory_readWord (a : ConstructorArgs) (off : Nat)
    (hin : off + 32 ≤ a.encoded.length) :
    (constructorArgumentMemory a).readWithPadding (480 + off) 32 =
      a.encoded.toByteArray.readWithPadding off 32 := by
  rw [readWithPadding_eq_extract _ _ (by rw [constructorArgumentMemory_size]; omega),
    readWithPadding_eq_extract _ _ (by rw [List.size_toByteArray]; omega),
    constructorArgumentMemory_extract]

theorem constructorArgumentMemory_free (a : ConstructorArgs) :
    memLoad ⟨64⟩ (constructorArgumentMemory a) = UInt256.ofNat (480 + a.encoded.length) := by
  have hbase : (constructorAllocatedMemory a).readWithPadding 64 32 =
      (UInt256.ofNat (480 + a.encoded.length)).toByteArray :=
    writeWord_sparse_read_back _ _ _
  have hr : (constructorArgumentMemory a).readWithPadding 64 32 =
      (constructorAllocatedMemory a).readWithPadding 64 32 := by
    rw [readWithPadding_eq_extract _ _ (by rw [constructorArgumentMemory_size]; omega),
      readWithPadding_eq_extract _ _ (by rw [constructorAllocatedMemory_size]),
      constructorArgumentMemory, extract_append_left _ _ _ _ (by
        rw [ByteArray.size_append, constructorAllocatedMemory_size, ByteArray_zeroes_size]; omega),
      extract_append_left _ _ _ _ (by rw [constructorAllocatedMemory_size])]
  exact loadedWord_of_read (by change 64 + 32 ≤ _; rw [constructorArgumentMemory_size]; omega)
    (hr.trans hbase)

set_option maxRecDepth 2000 in
theorem constructorReachArgumentMemory {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} (a : ConstructorArgs)
    (hcode : I.code = metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hbound : 23666 + a.encoded.length < UInt256.size)
    (hfit : SourceMemory.allocationFits ⟨480⟩ (UInt256.ofNat a.encoded.length)) :
    ∃ aw k C, RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g
      (initState σ σ₀ g A I) ⟨44⟩ [UInt256.ofNat (480 + a.encoded.length), ⟨480⟩]
      (constructorArgumentMemory a) aw ByteArray.empty σ k C := by
  have hsize : I.code.size < UInt256.size := by
    simpa only [hcode, ByteArray.size_append, metaMorphoV1_1CreationBytecode_size,
      List.size_toByteArray] using hbound
  have hsmall := (SourceMemory.constructorFirstAllocation_iff a hbound).mp hfit
  obtain ⟨aw, k, C, rd⟩ := constructorReachCopy (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hv hsize (by simpa only [List.size_toByteArray] using hfit)
  simp only [List.size_toByteArray, SourceMemory.constructorFirstCursor a hbound] at rd
  have hguard : UInt256.slt (UInt256.sub (⟨480⟩ + UInt256.ofNat a.encoded.length) ⟨480⟩)
      (UInt256.ofNat 192) = ⟨0⟩ := by
    rw [word_add_sub_left]
    apply slt_ofNat_lit_zero (by decide)
    · rw [a.encoded_length]; omega
    · have : 2 ^ 64 < 2 ^ 255 := by decide
      omega
  obtain ⟨aw', k', C', hd⟩ := metaMorphoV1_1Creation_block_29_fallthrough_packed
    (by decide) hguard rd
  have hadd : (⟨480⟩ : UInt256) + UInt256.ofNat a.encoded.length =
      UInt256.ofNat (480 + a.encoded.length) := by
    simpa only [SourceMemory.nextCursor,
      SourceMemory.roundedSize_aligned a.encoded_length_mod (by omega)] using
      SourceMemory.constructorFirstCursor a hbound
  change RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g
    (initState σ σ₀ g A I) ⟨44⟩ [⟨480⟩ + UInt256.ofNat a.encoded.length, ⟨480⟩]
    ((metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray).write
      23666 (constructorAllocatedMemory a) 480 (UInt256.ofNat a.encoded.length).toNat)
    aw' ByteArray.empty σ k' C' at hd
  rw [hadd, UInt256.toNat_ofNat_of_lt (show a.encoded.length < UInt256.size by omega),
    constructorCopyArguments] at hd
  exact ⟨aw', k', C', hd⟩

end Benchmarks.Morpho.MetaMorphoV1_1
