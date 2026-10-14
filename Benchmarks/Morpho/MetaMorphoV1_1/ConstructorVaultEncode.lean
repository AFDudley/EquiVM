import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStringEncoder

/-! Both vault metadata writers call the same creation-code string event encoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorVaultEncode {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (symbol : Bool) (src free : Nat)
    (buffer : StringBuffer mem src bytes) (hsmall : bytes.size < 2 ^ 64)
    (hsrc : src + 32 < UInt256.size) (hbelow : src + 32 ≤ free)
    (hfit : free + 64 + paddedSize bytes.size + 32 < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultEncodePC symbol)
      (UInt256.ofNat src :: constructorVaultEventPC symbol :: stringSetTopic symbol ::
        constructorVaultTail a symbol) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultEventPC symbol)
      (UInt256.ofNat (free + 64 + paddedSize bytes.size) :: UInt256.ofNat free ::
        UInt256.ofNat free :: stringSetTopic symbol :: constructorVaultTail a symbol)
      (stringReturnMemory mem (src + 32) free (UInt256.ofNat bytes.size)) aw' rdata σ k' C' := by
  have hn : (UInt256.ofNat bytes.size).toNat = bytes.size :=
    UInt256.toNat_ofNat_of_lt (by change bytes.size < 2 ^ 256; omega)
  have hentry : ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2760⟩
      (memLoad ⟨64⟩ mem :: UInt256.ofNat src :: constructorVaultEventPC symbol ::
        memLoad ⟨64⟩ mem :: memLoad ⟨64⟩ mem :: stringSetTopic symbol :: constructorVaultTail a symbol)
      mem aw' rdata σ k' C' := by
    cases symbol with
    | false => exact metaMorphoV1_1Creation_block_874_packed (by simp) (by native_decide) rd
    | true => exact metaMorphoV1_1Creation_block_999_packed (by simp) (by native_decide) rd
  obtain ⟨_, _, _, r1⟩ := hentry
  rw [hfree] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := constructorStringEncoder src free (UInt256.ofNat bytes.size)
    (by cases symbol <;> simp [constructorVaultTail]) (by rw [hn]; omega)
    hsrc (by have hsz := buffer.size; omega) hbelow (by rw [hn]; exact hfit) buffer.length
    (by cases symbol <;> native_decide) r1
  exact ⟨aw2, k2, C2, by simpa only [hn] using r2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
