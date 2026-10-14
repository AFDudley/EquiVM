import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultNameInit
import Benchmarks.Morpho.MetaMorphoV1_1.StringReturnMemory
import Benchmarks.Morpho.MetaMorphoV1_1.StringEncoderBytePrefix
import Benchmarks.Morpho.MetaMorphoV1_1.StringEncoderRoutines

/-! The creation-code ABI string encoder writes a header, payload, and zero padding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorStringEncoder {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256} (src dest : Nat) (len : UInt256)
    (hstack : R.length + 10 ≤ 1024) (hlen : len.toNat < 2 ^ 255)
    (hsrc : src + 32 < UInt256.size) (hmem : src + 32 ≤ mem.size) (hbelow : src + 32 ≤ dest)
    (hfit : dest + 64 + paddedSize len.toNat + 32 < UInt256.size)
    (hload : memLoad (UInt256.ofNat src) mem = len)
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2760⟩
      (UInt256.ofNat dest :: UInt256.ofNat src :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret
      (UInt256.ofNat (dest + 64 + paddedSize len.toNat) :: R)
      (stringReturnMemory mem (src + 32) dest len) aw' rdata σ k' C' := by
  have hp : len.toNat ≤ paddedSize len.toNat := by unfold paddedSize; omega
  have hf : dest < UInt256.size := by omega
  have hs : (UInt256.ofNat src).toNat = src := UInt256.toNat_ofNat_of_lt (by omega)
  have hl : memLoad (UInt256.ofNat src) ((UInt256.ofNat 32).toByteArray.write 0 mem dest 32) = len := by
    rw [memLoad_write_disjoint _ _ _ _ (by rw [hs]; exact hmem)
      (.inl (by rw [hs]; exact hbelow)), hload]
  have hzero : UInt256.ofNat 64 + (len + UInt256.ofNat dest) =
      UInt256.ofNat (dest + 64 + len.toNat) := by
    nth_rw 1 [← u256_ofNat_toNat len]
    rw [ofNat_add_words, ofNat_add_words]
    congr 1
    omega
  have hend : (UInt256.ofNat (paddedSize len.toNat) + UInt256.ofNat dest) +
      UInt256.ofNat 64 = UInt256.ofNat (dest + 64 + paddedSize len.toNat) := by
    rw [ofNat_add_words, ofNat_add_words]
    congr 1
    omega
  have hsource : (UInt256.ofNat src + UInt256.ofNat 32).toNat = src + 32 := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt hsrc]
  have hdest32 : (UInt256.ofNat dest + UInt256.ofNat 32).toNat = dest + 32 := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
  have hdest64 : (UInt256.ofNat dest + UInt256.ofNat 64).toNat = dest + 64 := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
  obtain ⟨aw', k', C', r1⟩ := metaMorphoV1_1Creation_block_2760_packed hstack hret rd
  refine ⟨aw', k', C', ?_⟩
  simpa only [metaMorphoV1_1Creation_block_2760_stack, metaMorphoV1_1Creation_block_2760_memory,
    UInt256.toNat_ofNat_of_lt hf, hl, stringEncoderRoundedSize len hlen, hzero, hend,
    hsource, hdest32, hdest64,
    UInt256.toNat_ofNat_of_lt (show dest + 64 + len.toNat < UInt256.size by omega),
    stringReturnMemory, stringReturnCopy, stringReturnHeader, Reasoning.Theory.writeWord] using r1

-- LIBRARY CANDIDATE: complete dynamic string encoding preserves earlier allocated byte windows.
theorem stringReturnMemory_bytePrefix (mem : ByteArray) (src dest : Nat) (len : UInt256)
    (hin : src + len.toNat ≤ mem.size) :
    ByteMemoryPrefix mem (stringReturnMemory mem src dest len) dest := by
  exact (byteMemoryPrefix_writeWord mem dest dest ⟨32⟩ (.inl (le_refl _))).trans
    ((stringPayloadMemory_bytePrefix (writeWord mem dest ⟨32⟩) src (dest + 32) len
      (by rw [writeWord_sparse_size]; omega)).mono (by omega))

-- LIBRARY CANDIDATE: ABI string encoding above the reserved words preserves the free pointer.
theorem stringReturnMemory_free (mem : ByteArray) (src dest : Nat) (len : UInt256)
    (hin : src + len.toNat ≤ mem.size) (hmem : 96 ≤ mem.size) (hlo : 96 ≤ dest) :
    memLoad ⟨64⟩ (stringReturnMemory mem src dest len) = memLoad ⟨64⟩ mem := by
  have hsize : 96 ≤ (stringReturnMemory mem src dest len).size :=
    le_trans hmem (stringReturnMemory_bytePrefix mem src dest len hin).size
  unfold memLoad
  rw [if_neg (by change ¬ 64 ≥ _; omega), if_neg (by change ¬ 64 ≥ mem.size; omega)]
  congr 2
  change (stringReturnMemory mem src dest len).readWithPadding 64 32 = mem.readWithPadding 64 32
  rw [stringReturnMemory, writeWord_sparse_read_preserved _ _ _ _
    (.inl ⟨by omega, by rw [stringReturnCopy_size _ _ _ _ hin]; omega⟩),
    stringReturnCopy_word _ _ _ _ _ hin (by omega), stringReturnHeader,
    writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨by omega, by rw [writeWord_sparse_size]; omega⟩),
    writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨hlo, hmem⟩)]

end Benchmarks.Morpho.MetaMorphoV1_1
