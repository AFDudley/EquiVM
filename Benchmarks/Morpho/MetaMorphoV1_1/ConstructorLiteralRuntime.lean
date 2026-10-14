import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorLiteralMemory
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStringDecode

/-! Allocation of the constructor's three empty strings and its version string. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem constructorLiteralAllocations {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {name symbol owner time morpho : UInt256} {R : List UInt256}
    (asset : AccountAddress) (ptr : Nat) (hstack : R.length + 18 ≤ 1024)
    (hlo : 96 ≤ ptr) (hptr : ptr < 2 ^ 64)
    (hfree : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨150⟩
      (symbol :: name :: owner :: time :: morpho :: UInt256.ofNat asset.val :: R)
      mem aw rdata σ k C) :
    (¬ ptr + 160 < 2 ^ 64 ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (ptr + 160 < 2 ^ 64 ∧ ∃ aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨229⟩
        (UInt256.ofNat (ptr + 32) :: UInt256.ofNat (ptr + 64) :: UInt256.ofNat ptr ::
          UInt256.ofNat (ptr + 96) :: owner :: morpho :: name :: symbol ::
          UInt256.ofNat asset.val :: time :: ⟨32⟩ :: ⟨64⟩ :: R)
        (constructorLiteralMemory mem ptr) aw' rdata σ k' C') := by
  have hword : ptr < UInt256.size := by change ptr < 2 ^ 256; omega
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hfree
  have r1 := metaMorphoV1_1Creation_block_150 (by omega) (by native_decide) rd
  simp only [metaMorphoV1_1Creation_block_150_stack, hfree] at r1
  by_cases h32 : ptr + 32 < 2 ^ 64
  · obtain ⟨aw2, k2, C2, r2⟩ := constructorAllocateReturn
      (by simp only [List.length_cons]; omega)
      ((alignedAllocationFitsNat ptr 32 hword (by decide) (by decide)).mpr h32)
      (by native_decide) r1
    rw [alignedAllocationCursor ptr 32 (by decide) (by decide)] at r2
    have h32word : ptr + 32 < UInt256.size := by change _ < 2 ^ 256; omega
    have hfree1 : memLoad (UInt256.ofNat 64) (emptyLiteralMemory mem ptr) =
        UInt256.ofNat (ptr + 32) := emptyLiteralMemory_free mem ptr hlo
    have haclean : UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)) (UInt256.ofNat asset.val) = UInt256.ofNat asset.val := by
      have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1) = solcAddrMask := by native_decide
      rw [hm, u256_land_comm]
      exact addressWord_val_clean asset
    obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_168_packed
      (by omega) (by native_decide) r2
    simp only [metaMorphoV1_1Creation_block_168_stack,
      metaMorphoV1_1Creation_block_168_memory, UInt256.toNat_ofNat_of_lt hword, haclean] at r3
    change RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2608⟩
      (memLoad (UInt256.ofNat 64) (emptyLiteralMemory mem ptr) :: ⟨32⟩ :: ⟨193⟩ ::
        memLoad (UInt256.ofNat 64) (emptyLiteralMemory mem ptr) :: owner :: morpho :: name ::
        symbol :: UInt256.ofNat asset.val :: time :: ⟨32⟩ :: UInt256.ofNat ptr :: R)
      (emptyLiteralMemory mem ptr) aw3 rdata σ k3 C3 at r3
    rw [hfree1] at r3
    by_cases h64 : ptr + 64 < 2 ^ 64
    · obtain ⟨aw4, k4, C4, r4⟩ := constructorAllocateReturn
        (by simp only [List.length_cons]; omega)
        ((alignedAllocationFitsNat (ptr + 32) 32 h32word (by decide) (by decide)).mpr (by omega))
        (by native_decide) r3
      rw [alignedAllocationCursor (ptr + 32) 32 (by decide) (by decide),
        show ptr + 32 + 32 = ptr + 64 by omega] at r4
      have h64word : ptr + 64 < UInt256.size := by change _ < 2 ^ 256; omega
      have hfree2 : memLoad (UInt256.ofNat 64)
          (emptyLiteralMemory (emptyLiteralMemory mem ptr) (ptr + 32)) =
          UInt256.ofNat (ptr + 64) := by
        simpa only [show ptr + 32 + 32 = ptr + 64 by omega] using
          emptyLiteralMemory_free (emptyLiteralMemory mem ptr) (ptr + 32) (by omega)
      obtain ⟨aw5, k5, C5, r5⟩ := metaMorphoV1_1Creation_block_193_packed
        (by omega) (by native_decide) r4
      simp only [metaMorphoV1_1Creation_block_193_stack,
        metaMorphoV1_1Creation_block_193_memory, UInt256.toNat_ofNat_of_lt h32word] at r5
      change RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2608⟩
        (memLoad (UInt256.ofNat 64)
            (writeWord (writeWord (emptyLiteralMemory mem ptr) 64 (UInt256.ofNat (ptr + 64)))
              (ptr + 32) ⟨0⟩) :: ⟨32⟩ :: ⟨210⟩ :: UInt256.ofNat ptr :: UInt256.ofNat (ptr + 32) ::
          owner :: morpho :: name :: symbol :: UInt256.ofNat asset.val :: time :: ⟨32⟩ ::
          memLoad (UInt256.ofNat 64)
            (writeWord (writeWord (emptyLiteralMemory mem ptr) 64 (UInt256.ofNat (ptr + 64)))
              (ptr + 32) ⟨0⟩) :: R)
        (writeWord (writeWord (emptyLiteralMemory mem ptr) 64 (UInt256.ofNat (ptr + 64)))
          (ptr + 32) ⟨0⟩) aw5 rdata σ k5 C5 at r5
      have hm2 : writeWord (writeWord (emptyLiteralMemory mem ptr) 64 (UInt256.ofNat (ptr + 64)))
          (ptr + 32) ⟨0⟩ = emptyLiteralMemory (emptyLiteralMemory mem ptr) (ptr + 32) := by
        simp only [emptyLiteralMemory, show ptr + 32 + 32 = ptr + 64 by omega]
      rw [hm2, hfree2] at r5
      by_cases h96 : ptr + 96 < 2 ^ 64
      · obtain ⟨aw6, k6, C6, r6⟩ := constructorAllocateReturn
          (by simp only [List.length_cons]; omega)
          ((alignedAllocationFitsNat (ptr + 64) 32 h64word (by decide) (by decide)).mpr (by omega))
          (by native_decide) r5
        rw [alignedAllocationCursor (ptr + 64) 32 (by decide) (by decide),
          show ptr + 64 + 32 = ptr + 96 by omega] at r6
        have h96word : ptr + 96 < UInt256.size := by change _ < 2 ^ 256; omega
        have hfree3 : memLoad (UInt256.ofNat 64)
            (emptyLiteralMemory (emptyLiteralMemory (emptyLiteralMemory mem ptr) (ptr + 32))
              (ptr + 64)) = UInt256.ofNat (ptr + 96) := by
          simpa only [show ptr + 64 + 32 = ptr + 96 by omega] using
            emptyLiteralMemory_free _ (ptr + 64) (by omega)
        obtain ⟨aw7, k7, C7, r7⟩ := metaMorphoV1_1Creation_block_210_packed
          (by omega) (by native_decide) r6
        simp only [metaMorphoV1_1Creation_block_210_stack,
          metaMorphoV1_1Creation_block_210_memory, UInt256.toNat_ofNat_of_lt h64word] at r7
        have hm3 : writeWord
            (writeWord (emptyLiteralMemory (emptyLiteralMemory mem ptr) (ptr + 32)) 64
              (UInt256.ofNat (ptr + 96))) (ptr + 64) ⟨0⟩ =
            emptyLiteralMemory (emptyLiteralMemory (emptyLiteralMemory mem ptr) (ptr + 32))
              (ptr + 64) := by
          simp only [emptyLiteralMemory, show ptr + 64 + 32 = ptr + 96 by omega]
        change RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2608⟩
          (memLoad (UInt256.ofNat 64)
              (writeWord (writeWord
                (emptyLiteralMemory (emptyLiteralMemory mem ptr) (ptr + 32)) 64
                  (UInt256.ofNat (ptr + 96))) (ptr + 64) ⟨0⟩) :: ⟨64⟩ :: ⟨229⟩ ::
            UInt256.ofNat (ptr + 32) :: UInt256.ofNat (ptr + 64) :: UInt256.ofNat ptr ::
            memLoad (UInt256.ofNat 64)
              (writeWord (writeWord
                (emptyLiteralMemory (emptyLiteralMemory mem ptr) (ptr + 32)) 64
                  (UInt256.ofNat (ptr + 96))) (ptr + 64) ⟨0⟩) ::
            owner :: morpho :: name :: symbol :: UInt256.ofNat asset.val :: time :: ⟨32⟩ :: ⟨64⟩ :: R)
          (writeWord (writeWord (emptyLiteralMemory (emptyLiteralMemory mem ptr) (ptr + 32)) 64
            (UInt256.ofNat (ptr + 96))) (ptr + 64) ⟨0⟩) aw7 rdata σ k7 C7 at r7
        rw [hm3, hfree3] at r7
        by_cases h160 : ptr + 160 < 2 ^ 64
        · obtain ⟨aw8, k8, C8, r8⟩ := constructorAllocateReturn
            (by simp only [List.length_cons]; omega)
            ((alignedAllocationFitsNat (ptr + 96) 64 h96word (by decide) (by decide)).mpr (by omega))
            (by native_decide) r7
          rw [alignedAllocationCursor (ptr + 96) 64 (by decide) (by decide),
            show ptr + 96 + 64 = ptr + 160 by omega] at r8
          exact .inr ⟨h160, aw8, k8, C8, r8⟩
        · exact .inl ⟨h160, constructorAllocateRevert
            (by simp only [List.length_cons]; omega)
            (fun h => h160 (by
              have := (alignedAllocationFitsNat (ptr + 96) 64 h96word (by decide) (by decide)).mp h
              omega)) r7⟩
      · exact .inl ⟨by omega, constructorAllocateRevert
          (by simp only [List.length_cons]; omega)
          (fun h => h96 (by
            have := (alignedAllocationFitsNat (ptr + 64) 32 h64word (by decide) (by decide)).mp h
            omega)) r5⟩
    · exact .inl ⟨by omega, constructorAllocateRevert
        (by simp only [List.length_cons]; omega)
        (fun h => h64 (by
          have := (alignedAllocationFitsNat (ptr + 32) 32 h32word (by decide) (by decide)).mp h
          omega)) r3⟩
  · exact .inl ⟨by omega, constructorAllocateRevert
      (by simp only [List.length_cons]; omega)
      (fun h => h32 ((alignedAllocationFitsNat ptr 32 hword (by decide) (by decide)).mp h)) r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
