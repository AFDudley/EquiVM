import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayEncodeRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.MulticallReturnMemory

/-! Encode and return the accumulated multicall results. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem multicallReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr : UInt256} {σ : AccountMap} {k C : Nat}
    {bs : List ByteArray} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 25 ≤ 1024)
    (hm : MulticallMemory mem ptr bs)
    (rd : RD (deployedRuntime v) I g s0 ⟨4003⟩
      (x0 :: x1 :: x2 :: x3 :: ⟨128⟩ :: R) mem aw out σ k C) :
    RDret (deployedRuntime v) g s0 σ (bytesArrayReturnBytes bs) := by
  have hfit := hm.returnBound
  have hlo := hm.lower
  have hb := hm.bound
  have hn : bs.length < UInt256.size := by change _ < 2 ^ 256; omega
  have hptr : ptr.toNat < UInt256.size := ptr.val.isLt
  have h32 : 32 * bs.length < UInt256.size := by omega
  have hload : memLoad ⟨128⟩ (writeWord mem ptr.toNat ⟨32⟩) = UInt256.ofNat bs.length := by
    rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
      (by change 160 ≤ mem.size; have := hm.size; omega)
      (.inl (by change 160 ≤ ptr.toNat; omega))]
    exact hm.length
  have hadd32 : ptr + UInt256.ofNat 32 = UInt256.ofNat (ptr.toNat + 32) := by
    nth_rw 1 [← u256_ofNat_toNat ptr]
    exact ofNat_add_words _ _
  have hadd64 : ptr + UInt256.ofNat 64 = UInt256.ofNat (ptr.toNat + 64) := by
    nth_rw 1 [← u256_ofNat_toNat ptr]
    exact ofNat_add_words _ _
  have htail : ptr + UInt256.shiftLeft (UInt256.ofNat bs.length) (UInt256.ofNat 5) +
      UInt256.ofNat 64 = UInt256.ofNat (ptr.toNat + 64 + 32 * bs.length) := by
    have hshift : UInt256.shiftLeft (UInt256.ofNat bs.length) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * bs.length) := shiftLeft5_ofNat_eq h32
    rw [hshift]
    nth_rw 1 [← u256_ofNat_toNat ptr]
    rw [ofNat_add_words, ofNat_add_words]
    congr 1
    omega
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_4003_packed
    (immWords := wordsOf (immStore v)) (by omega) rd
  have hfree : memLoad (UInt256.ofNat 64) mem = ptr := hm.free
  have hload' : memLoad (⟨128⟩ : UInt256)
      ((UInt256.ofNat 32).toByteArray.write 0 mem ptr.toNat 32) = UInt256.ofNat bs.length := hload
  simp only [metaMorphoV1_1_block_4003_stack, metaMorphoV1_1_block_4003_memory,
    hfree, hload', hadd32, hadd64, htail,
    UInt256.toNat_ofNat_of_lt (show ptr.toNat + 32 < UInt256.size by omega)] at r1
  have r1' : RD (deployedRuntime v) I g s0 ⟨4044⟩
      (UInt256.ofNat (ptr.toNat + 64) :: ⟨0⟩ :: UInt256.ofNat bs.length :: ⟨160⟩ ::
        UInt256.ofNat (ptr.toNat + 64 + 32 * bs.length) :: ptr :: ptr ::
          x0 :: x1 :: x2 :: x3 :: ⟨128⟩ :: R)
      (multicallReturnStart mem ptr.toNat bs.length) aw1 out σ k1 C1 := r1
  rw [← u256_ofNat_toNat ptr] at r1'
  simp only [UInt256.toNat_ofNat_of_lt hptr] at r1'
  have hs := hm.sources.preserve hptr (multicallReturnStart_prefix mem ptr.toNat bs.length)
  obtain ⟨aw2, k2, C2, r2⟩ := bytesArrayEncodeLoop (head := ptr.toNat + 64)
    (tail := ptr.toNat + 64 + 32 * bs.length) (origin := ptr.toNat)
    (R := x0 :: x1 :: x2 :: x3 :: ⟨128⟩ :: R) v
    (by simp only [List.length_cons]; omega) hs hptr (by omega) (le_refl _) (by omega)
    hfit hn (Nat.zero_add _).symm r1'
  have hret := metaMorphoV1_1_block_4052 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) r2
  have he : UInt256.sub
      (UInt256.ofNat (ptr.toNat + 64 + 32 * bs.length + (bytesArrayTails bs).size))
      (UInt256.ofNat ptr.toNat) = UInt256.ofNat (64 + 32 * bs.length + (bytesArrayTails bs).size) := by
    rw [ofNat_sub_words (by omega) (by omega)]
    congr 1
    omega
  have hr := multicallReturnMemory_read hm
  dsimp only [multicallReturnMemory] at hr
  simpa only [he, UInt256.toNat_ofNat_of_lt hptr,
    UInt256.toNat_ofNat_of_lt (show 64 + 32 * bs.length + (bytesArrayTails bs).size < UInt256.size by omega),
    hr] using hret

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
