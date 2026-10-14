import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultSymbolInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsCall
import Benchmarks.Morpho.MetaMorphoV1_1.BoundedCallMemory

/-! The symbol event, MORPHO immutable word, and strict decimals request. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorMorphoMemory (mem : ByteArray) (morpho : AccountAddress) (ptr : UInt256) : ByteArray :=
  writeWord (writeWord mem 416 (UInt256.ofNat morpho.val)) ptr.toNat constructorDecimalsSelectorWord

theorem constructorMorphoRequest {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr finish : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (hperm : I.perm = true) (hmem : 96 ≤ mem.size)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1010⟩
      [finish, ptr, ptr, stringSetTopic true, UInt256.ofNat a.asset.val,
        UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩] mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1039⟩
      [gasArg, UInt256.ofNat a.asset.val, ptr, ⟨4⟩, ptr, ⟨32⟩,
        ptr, UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]
      (constructorMorphoMemory mem a.morpho ptr) aw' rdata σ k' C' := by
  have hf : memLoad ⟨64⟩ (writeWord mem 416 (UInt256.ofNat a.morpho.val)) = ptr :=
    (memLoad_writeWord_disjoint mem 416 ⟨64⟩ _ hmem (.inl (by decide))).trans hfree
  obtain ⟨aw', k', C', r1⟩ := metaMorphoV1_1Creation_block_1010_packed (by decide) hperm rd
  simp only [metaMorphoV1_1Creation_block_1010_stack,
    metaMorphoV1_1Creation_block_1010_memory] at r1
  change RD _ I g s0 ⟨1039⟩
    [_ , UInt256.ofNat a.asset.val, memLoad ⟨64⟩ (writeWord mem 416 (UInt256.ofNat a.morpho.val)),
      ⟨4⟩, memLoad ⟨64⟩ (writeWord mem 416 (UInt256.ofNat a.morpho.val)), ⟨32⟩,
      memLoad ⟨64⟩ (writeWord mem 416 (UInt256.ofNat a.morpho.val)),
      UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]
    (writeWord (writeWord mem 416 (UInt256.ofNat a.morpho.val))
      (memLoad ⟨64⟩ (writeWord mem 416 (UInt256.ofNat a.morpho.val))).toNat
      constructorDecimalsSelectorWord) aw' rdata σ k' C' at r1
  rw [hf] at r1
  exact ⟨_, aw', k', C', r1⟩

theorem constructorStrictDecimalsCall {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr gasArg : UInt256} {R : List UInt256} (asset : AccountAddress)
    (hstack : R.length + 1 ≤ 1024) (hs : SourceState s0 I σ evm)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1039⟩
      (gasArg :: UInt256.ofNat asset.val :: ptr :: ⟨4⟩ :: ptr :: ⟨32⟩ :: R)
      (writeWord mem ptr.toNat constructorDecimalsSelectorWord) aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm asset "decimals" 0 [] (ok, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < 2 ^ 138 ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1040⟩
        ((if ok then ⟨1⟩ else ⟨0⟩) :: R)
        (fixedReturnBuffer (writeWord mem ptr.toNat constructorDecimalsSelectorWord) ptr out 32)
        aw' out evm'.accountMap k' C' := by
  obtain ⟨evm', ok, out, aw', k', C', hc, hs', _, r1⟩ :=
    typedStaticcallSimulation (cfg := config) (address := asset) (name := "decimals") (args := [])
      hstack
      (decode_append_left_of_decode _ _ _ _ _ (by native_decide)
        (by rw [metaMorphoV1_1CreationBytecode_size]; native_decide) (by native_decide))
      hs
      (by rw [accountAddress_ofUInt256_eq_ofNat_toNat]; exact (addressOfWordOfNat _).symm)
      (by rw [constructorDecimalsEncode]; congr 1
          simpa only [Nat.add_zero] using
            (writeWord_sparse_read_window mem ptr.toNat 0 4 constructorDecimalsSelectorWord
              (by decide) (by decide) (by decide)).symm) rd
  have hout : out.size < 2 ^ 138 := by
    obtain ⟨input, he, hcall⟩ := hc
    rw [constructorDecimalsEncode, Option.some.injEq] at he
    subst input
    exact callViaEVM_output_bound hcall
      (by simp only [ByteArray.size_extract, toByteArray_size]; decide)
  exact ⟨evm', ok, out, aw', k', C', hc, hs', hout, r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
