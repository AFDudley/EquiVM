import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayEncodeRead
import Benchmarks.Morpho.MetaMorphoV1_1.StringEncoderRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_023

/-! The multicall return encoder traverses its pointer table and encodes each byte buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: normalization of a dynamic-array relative offset after its two headers.
theorem bytesArrayRelativeOutput (tail origin : Nat) (ho : origin + 64 ≤ tail)
    (hb : tail < UInt256.size) :
    UInt256.sub (UInt256.ofNat tail) (UInt256.ofNat origin) + UInt256.lnot (UInt256.ofNat 63) =
      UInt256.ofNat (tail - origin - 64) := by
  rw [ofNat_sub_words (by omega) hb,
    show UInt256.lnot (UInt256.ofNat 63) = UInt256.ofNat (UInt256.size - 64) by decide +kernel,
    u256_add_comm]
  exact ofNat_size_sub_add (by decide) (by omega) (by omega)

theorem bytesArrayEncodeLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {slot head tail origin limit i n : Nat} {bs : List ByteArray} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 20 ≤ 1024)
    (hs : BytesArraySources mem slot limit bs) (hb : limit < UInt256.size)
    (hh : limit ≤ head) (ht : head + 32 * bs.length ≤ tail) (ho : origin + 64 ≤ head)
    (hfit : tail + (bytesArrayTails bs).size + 32 < UInt256.size)
    (hn : n < UInt256.size) (hi : n = i + bs.length)
    (rd : RD (deployedRuntime v) I g s0 ⟨4044⟩
      (UInt256.ofNat head :: UInt256.ofNat i :: UInt256.ofNat n :: UInt256.ofNat slot ::
        UInt256.ofNat tail :: UInt256.ofNat origin :: UInt256.ofNat origin :: R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨4052⟩
      (UInt256.ofNat (head + 32 * bs.length) :: UInt256.ofNat n :: UInt256.ofNat n ::
        UInt256.ofNat (slot + 32 * bs.length) :: UInt256.ofNat (tail + (bytesArrayTails bs).size) ::
        UInt256.ofNat origin :: UInt256.ofNat origin :: R)
      (bytesArrayEncodeMemory mem slot head tail origin bs) aw' out σ k' C' := by
  induction bs generalizing mem aw k C slot head tail i with
  | nil =>
      have he : i = n := by simp only [List.length_nil] at hi; omega
      subst i
      obtain ⟨aw', k', C', r⟩ := metaMorphoV1_1_block_4044_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (ult_zero (le_refl _)) rd
      exact ⟨aw', k', C', r⟩
  | cons b bs ih =>
      have hit : i < n := by simp only [List.length_cons] at hi; omega
      have ht' : head + 32 ≤ tail := by simp only [List.length_cons] at ht; omega
      have htail : tail < UInt256.size := by omega
      have hhead : head < UInt256.size := by omega
      obtain ⟨p, hlo, hend, hlen, hbuf, hslot⟩ := hs.data 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at hend hlen hbuf hslot
      have hlen' : b.size < UInt256.size := lt_trans hlen (by decide)
      let mid := writeWord mem head (UInt256.ofNat (tail - origin - 64))
      have hm : memLoad (UInt256.ofNat slot) mid = p := by
        dsimp only [mid]
        rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
          (by rw [UInt256.toNat_ofNat_of_lt (by have := hs.bound; omega)]
              have he := hs.size; simp only [List.length_cons] at he; omega)
          (.inl (by rw [UInt256.toNat_ofNat_of_lt (by have := hs.bound; omega)]
                    have he := hs.bound; simp only [List.length_cons] at he; omega))]
        exact hslot
      have hbuf' : BytesBuffer mid p b := hbuf.writeWord _ _ (.inl (by omega))
      have r1 := metaMorphoV1_1_block_4044_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [ult_one (by rw [UInt256.toNat_ofNat_of_lt (by omega),
              UInt256.toNat_ofNat_of_lt hn]; exact hit)]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1_block_4059_packed
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
      have r2' : RD (deployedRuntime v) I g s0 ⟨11086⟩
          (p :: UInt256.ofNat tail :: ⟨4090⟩ :: ⟨32⟩ :: ⟨32⟩ :: ⟨1⟩ :: UInt256.ofNat head ::
            UInt256.ofNat i :: UInt256.ofNat n :: UInt256.ofNat slot :: UInt256.ofNat origin :: R)
          mid aw2 out σ k2 C2 := by
        simp only [metaMorphoV1_1_block_4059_stack, metaMorphoV1_1_block_4059_memory,
          bytesArrayRelativeOutput tail origin (by omega) htail,
          UInt256.toNat_ofNat_of_lt hhead] at r2
        change RD (deployedRuntime v) I g s0 ⟨11086⟩
          (memLoad (UInt256.ofNat slot) mid :: UInt256.ofNat tail :: ⟨4090⟩ :: ⟨32⟩ :: ⟨32⟩ ::
            ⟨1⟩ :: UInt256.ofNat head :: UInt256.ofNat i :: UInt256.ofNat n ::
              UInt256.ofNat slot :: UInt256.ofNat origin :: R) mid aw2 out σ k2 C2 at r2
        rwa [hm] at r2
      rw [← u256_ofNat_toNat p] at r2'
      obtain ⟨aw3, k3, C3, r3⟩ := stringEncoderRoutine v p.toNat tail (UInt256.ofNat b.size)
        (by simp only [List.length_cons]; omega)
        (by rw [UInt256.toNat_ofNat_of_lt hlen']; exact lt_trans hlen (by decide))
        (by omega)
        (by rw [UInt256.toNat_ofNat_of_lt hlen']; rw [bytesArrayTails_size_cons] at hfit; omega)
        (by simpa only [u256_ofNat_toNat] using hbuf'.length)
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r2'
      rw [UInt256.toNat_ofNat_of_lt hlen'] at r3
      have he : stringPayloadMemory mid (p.toNat + 32) tail (UInt256.ofNat b.size) =
          bytesArrayEncodeStep mem slot head tail origin b := by
        simp only [bytesArrayEncodeStep, hslot, mid]
      rw [he] at r3
      have r4 := metaMorphoV1_1_block_4090 (immWords := wordsOf (immStore v))
        (by omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r3
      simp only [metaMorphoV1_1_block_4090_stack,
        show UInt256.ofNat head + (⟨32⟩ : UInt256) = UInt256.ofNat (head + 32) from ofNat_add_words _ _,
        show UInt256.ofNat slot + (⟨32⟩ : UInt256) = UInt256.ofNat (slot + 32) from ofNat_add_words _ _,
        show UInt256.ofNat i + (⟨1⟩ : UInt256) = UInt256.ofNat (i + 1) from ofNat_add_words _ _] at r4
      have hp := bytesArrayEncodeStep_prefix hs hh ht' (origin := origin)
      obtain ⟨aw5, k5, C5, r5⟩ := ih (head := head + 32) (tail := tail + 32 + paddedSize b.size)
        (i := i + 1) ((hs.preserve hb (hp.mono hh)).tail) (by omega)
        (by simp only [List.length_cons] at ht; omega) (by omega)
        (by rw [bytesArrayTails_size_cons] at hfit; omega)
        (by simp only [List.length_cons] at hi; omega) r4
      refine ⟨aw5, k5, C5, ?_⟩
      simpa only [bytesArrayEncodeMemory, List.length_cons, bytesArrayTails_size_cons,
        show head + 32 + 32 * bs.length = head + 32 * (bs.length + 1) by omega,
        show slot + 32 + 32 * bs.length = slot + 32 * (bs.length + 1) by omega,
        show tail + 32 + paddedSize b.size + (bytesArrayTails bs).size =
          tail + (32 + paddedSize b.size + (bytesArrayTails bs).size) by omega] using r5

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
