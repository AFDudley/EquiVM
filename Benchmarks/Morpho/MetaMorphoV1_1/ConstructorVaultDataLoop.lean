import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultClear

/-! Write every complete word of a long vault name or symbol. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorVaultDataLoopPC (symbol : Bool) : UInt256 := if symbol then ⟨1644⟩ else ⟨1901⟩
def constructorVaultDataExitPC (symbol : Bool) : UInt256 := if symbol then ⟨1653⟩ else ⟨1910⟩

theorem constructorVaultDataLoopExit {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {off cutoff stride slot len ptr : UInt256} (a : ConstructorArgs) (symbol : Bool)
    (hcond : UInt256.lt off cutoff = ⟨0⟩)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultDataLoopPC symbol)
      (off :: cutoff :: stride :: slot :: len :: ptr :: constructorVaultTail a symbol)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultDataExitPC symbol)
      (⟨32⟩ :: off :: cutoff :: stride :: slot :: len :: ptr :: constructorVaultTail a symbol)
      mem aw' rdata σ k' C' := by
  cases symbol with
  | false => exact metaMorphoV1_1Creation_block_1901_fallthrough_packed (by simp) hcond rd
  | true => exact metaMorphoV1_1Creation_block_1644_fallthrough_packed (by simp) hcond rd

theorem constructorVaultDataLoopStep {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {off cutoff stride slot len ptr : UInt256} (a : ConstructorArgs) (symbol : Bool)
    (hperm : I.perm = true) (hcond : UInt256.lt off cutoff ≠ ⟨0⟩)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultDataLoopPC symbol)
      (off :: cutoff :: stride :: slot :: len :: ptr :: constructorVaultTail a symbol)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultDataLoopPC symbol)
      ((off + UInt256.ofNat 32) :: cutoff :: (stride + UInt256.ofNat 32) ::
        (slot + UInt256.ofNat 1) :: len :: ptr :: constructorVaultTail a symbol)
      mem aw' rdata (sstoreAccountMap I.codeOwner σ slot (memLoad (ptr + stride) mem)) k' C' := by
  cases symbol with
  | false =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_1901_taken_packed
      (by simp) hcond (by native_decide) rd
    exact metaMorphoV1_1Creation_block_1979_packed
      (by simp [constructorVaultTail]) hperm (by native_decide) r1
  | true =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_1644_taken_packed
      (by simp) hcond (by native_decide) rd
    exact metaMorphoV1_1Creation_block_1722_packed
      (by simp [constructorVaultTail]) hperm (by native_decide) r1

theorem constructorVaultDataWords {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {base cutoff len ptr : UInt256} (a : ConstructorArgs) (symbol : Bool) (n i : Nat)
    (hperm : I.perm = true) (buffer : StringBuffer mem ptr.toNat bytes)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size)
    (hfull : (i + n) * 32 ≤ bytes.size) (hcut : cutoff.toNat = 32 * (i + n))
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultDataLoopPC symbol)
      (UInt256.ofNat (32 * i) :: cutoff :: UInt256.ofNat (32 * (i + 1)) ::
        solidityBytesDataSlot base i :: len :: ptr :: constructorVaultTail a symbol)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultDataExitPC symbol)
      (⟨32⟩ :: UInt256.ofNat (32 * (i + n)) :: cutoff :: UInt256.ofNat (32 * (i + n + 1)) ::
        solidityBytesDataSlot base (i + n) :: len :: ptr :: constructorVaultTail a symbol)
      mem aw' rdata (solidityDataWordsForwardFrom I.codeOwner σ base bytes i n) k' C' := by
  induction n generalizing i aw k C σ with
  | zero =>
    simpa only [Nat.add_zero, solidityDataWordsForwardFrom] using
      constructorVaultDataLoopExit a symbol
        (ult_zero (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)) rd
  | succ n ih =>
    have hi : 32 * i + 32 ≤ bytes.size := by omega
    have hw : memLoad (ptr + UInt256.ofNat (32 * (i + 1))) mem =
        uInt256OfByteArray (bytes.readWithPadding (i * 32) 32) := by
      rw [show 32 * (i + 1) = 32 + 32 * i by omega, buffer.word hfit (32 * i) hi]
      rw [Nat.mul_comm i 32]
    obtain ⟨_, _, _, r1⟩ := constructorVaultDataLoopStep a symbol hperm
      (by rw [ult_one (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)]; decide) rd
    have hslot : solidityBytesDataSlot base i + UInt256.ofNat 1 =
        solidityBytesDataSlot base (i + 1) := by
      unfold solidityBytesDataSlot
      rw [u256_add_assoc, ofNat_add_words]
    simp only [hw, hslot, ofNat_add_words,
      show 32 * i + 32 = 32 * (i + 1) by omega,
      show 32 * (i + 1) + 32 = 32 * (i + 1 + 1) by omega] at r1
    obtain ⟨aw2, k2, C2, r2⟩ := ih (i + 1) (by omega) (by omega) r1
    exact ⟨aw2, k2, C2, by
      simpa only [solidityDataWordsForwardFrom,
        show i + 1 + n = i + (n + 1) by omega] using r2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
