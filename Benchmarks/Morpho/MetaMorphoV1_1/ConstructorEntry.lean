import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorEncoding
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_001
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_006

/-! Constructor entry, exact argument length, and the nonpayable failure path. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

-- LIBRARY CANDIDATE: constructor revert packaging for arbitrary parameters and runtime layout.
theorem constructorRefinementOfRevert {cfg : Config} {decl : ContractDecl}
    {args : List Value} {runtimeCodeOf : Store → ByteArray}
    {code : ByteArray} {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = code)
    (hevm : RDrev code (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hsource : steleCtorExec cfg decl args σ σ₀ g A I .reverted) :
    typedConstructorRefinementFor cfg decl args σ σ₀ g A I runtimeCodeOf := by
  obtain hoog | ⟨s, out, hX⟩ := hevm
  · exact .outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hoog; exact hoog))
  · have hxi := Xi_revert_of_X (g := g) (by rw [← hcode] at hX; exact hX)
    exact .execution hxi hsource (.revert rfl rfl) trivial

theorem constructorNonpayable {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (a : ConstructorArgs)
    (hcode : I.code = metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray)
    (hv : I.weiValue ≠ ⟨0⟩) :
    typedConstructorRefinementFor config contract a.values σ σ₀ g A I
      (immutableLayout.deployed metaMorphoV1_1Bytecode) := by
  have h0 := RD.initState (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have h1 := metaMorphoV1_1Creation_block_0_taken (by decide) hv (by native_decide) h0
  have hr := metaMorphoV1_1Creation_block_1596 (by decide) h1
  apply constructorRefinementOfRevert hcode hr
  refine .intro rfl a.values_length rfl ?_
  exact bodyReverts_nonPayable hv

def constructorInitialMemory : ByteArray := writeWord ByteArray.empty 64 ⟨480⟩

theorem constructorReachAllocator {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {tail : ByteArray}
    (hcode : I.code = metaMorphoV1_1CreationBytecode ++ tail)
    (hv : I.weiValue = ⟨0⟩) (hsize : I.code.size < UInt256.size) :
    ∃ aw k C, RD (metaMorphoV1_1CreationBytecode ++ tail) I g (initState σ σ₀ g A I)
      ⟨2608⟩ [⟨480⟩, UInt256.ofNat tail.size, ⟨29⟩, ⟨23666⟩,
        UInt256.ofNat tail.size, UInt256.ofNat tail.size, ⟨480⟩]
      constructorInitialMemory aw ByteArray.empty σ k C := by
  have h0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have h1 := metaMorphoV1_1Creation_block_0_fallthrough (by decide) hv h0
  obtain ⟨aw, k, C, h2⟩ := metaMorphoV1_1Creation_block_12_packed
    (by decide) (by native_decide) h1
  have hlen := constructorCodeSize (tail := tail) (by rwa [← hcode])
  refine ⟨aw, k, C, ?_⟩
  simpa only [metaMorphoV1_1Creation_block_12_stack, hlen] using h2

theorem constructorReachCopy {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {tail : ByteArray}
    (hcode : I.code = metaMorphoV1_1CreationBytecode ++ tail)
    (hv : I.weiValue = ⟨0⟩) (hsize : I.code.size < UInt256.size)
    (hfit : SourceMemory.allocationFits ⟨480⟩ (UInt256.ofNat tail.size)) :
    ∃ aw k C, RD (metaMorphoV1_1CreationBytecode ++ tail) I g (initState σ σ₀ g A I)
      ⟨29⟩ [⟨23666⟩, UInt256.ofNat tail.size, UInt256.ofNat tail.size, ⟨480⟩]
      (writeWord constructorInitialMemory 64
        (SourceMemory.nextCursor ⟨480⟩ (UInt256.ofNat tail.size)))
      aw ByteArray.empty σ k C := by
  obtain ⟨aw, k, C, rd⟩ := constructorReachAllocator (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hv hsize
  exact SourceMemory.constructorAllocateReturn (by simp) hfit (by native_decide) rd

theorem constructorInitialAllocationRevert {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {tail : ByteArray}
    (hcode : I.code = metaMorphoV1_1CreationBytecode ++ tail)
    (hv : I.weiValue = ⟨0⟩) (hsize : I.code.size < UInt256.size)
    (hfit : ¬ SourceMemory.allocationFits ⟨480⟩ (UInt256.ofNat tail.size)) :
    RDrev (metaMorphoV1_1CreationBytecode ++ tail) g (initState σ σ₀ g A I) := by
  obtain ⟨aw, k, C, rd⟩ := constructorReachAllocator (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hv hsize
  exact SourceMemory.constructorAllocateRevert (by simp) hfit rd

end Benchmarks.Morpho.MetaMorphoV1_1
