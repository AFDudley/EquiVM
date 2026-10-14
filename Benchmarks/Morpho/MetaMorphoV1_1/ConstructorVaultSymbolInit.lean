import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultNameEvent

/-! Initialize the vault symbol and encode its event, ready for the final immutable setup. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorVaultSymbolInit {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ok : Bool) (out : ByteArray) (free : Nat)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (hfreeBound : free < 2 ^ 64) (hbelow : a.stringsEnd ≤ free)
    (buffer : StringBuffer mem a.nameEnd a.symbol)
    (hfree : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨905⟩
      (UInt256.ofNat a.symbol.size :: UInt256.ofNat a.nameEnd :: constructorVaultTail a true)
      mem aw rdata σ k C) :
    (ExecBlock config (constructorTimelockReadyFrame a ok out I) evm (contract.ctor.body.drop 31) .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    ((∀ result, ExecBlock config (constructorTimelockReadyFrame a ok out I)
        (storageStringWriteState evm ⟨25⟩ a.symbol) (contract.ctor.body.drop 32) result →
      ExecBlock config (constructorTimelockReadyFrame a ok out I) evm (contract.ctor.body.drop 31) result) ∧
      SourceState s0 I (storageStringWriteState evm ⟨25⟩ a.symbol).accountMap
        (storageStringWriteState evm ⟨25⟩ a.symbol) ∧
      ∃ mem' aw' k' C', ByteMemoryPrefix mem mem' free ∧
        memLoad ⟨64⟩ mem' = UInt256.ofNat free ∧
        RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1010⟩
          (UInt256.ofNat (free + 64 + paddedSize a.symbol.size) :: UInt256.ofNat free ::
            UInt256.ofNat free :: stringSetTopic true :: constructorVaultTail a true)
          mem' aw' rdata (storageStringWriteState evm ⟨25⟩ a.symbol).accountMap k' C') := by
  have hbytes := (a.string_sizes_small hsmall).2
  have hn : (UInt256.ofNat a.nameEnd).toNat = a.nameEnd :=
    UInt256.toNat_ofNat_of_lt (by change a.nameEnd < 2 ^ 256; omega)
  have hl : (UInt256.ofNat a.symbol.size).toNat = a.symbol.size :=
    UInt256.toNat_ofNat_of_lt (by change a.symbol.size < 2 ^ 256; omega)
  have hlo : 96 ≤ a.nameEnd := by
    unfold ConstructorArgs.nameEnd ConstructorArgs.argumentEnd; omega
  have hpad : a.symbol.size ≤ paddedSize a.symbol.size := by unfold paddedSize; omega
  rcases constructorVaultAssignInit (frame := constructorTimelockReadyFrame a ok out I)
      a true hs hperm (constructorTimelockReadyFrame_contract a ok out I)
      (constructorTimelockReadyFrame_string a ok out I true)
      (constructorTimelockReadyFrame_unshadowed a ok out I true)
      (by simpa only [hn] using buffer) (by rw [hn]; exact hlo)
      (by rw [hn]; change a.nameEnd + 32 + a.symbol.size < 2 ^ 256; omega)
      hbytes rd with hfail | hsuccess
  · exact .inl hfail
  · obtain ⟨hsource, hs', mem1, _, _, _, hb, hp, hf, r1⟩ := hsuccess
    have hb1 : StringBuffer mem1 a.nameEnd a.symbol := by simpa only [hn] using hb
    have hin : a.nameEnd + 32 + (UInt256.ofNat a.symbol.size).toNat ≤ mem1.size := by
      rw [hl]; have hsz := hb1.size; omega
    have hf1 := hf.trans hfree
    obtain ⟨aw2, k2, C2, r2⟩ := constructorVaultEncode a true a.nameEnd free hb1 hbytes
      (by change a.nameEnd + 32 < 2 ^ 256; omega)
      (by unfold ConstructorArgs.stringsEnd at hbelow; omega)
      (by change free + 64 + paddedSize a.symbol.size + 32 < 2 ^ 256; unfold paddedSize; omega)
      hf1 r1
    have hp2 := stringReturnMemory_bytePrefix mem1 (a.nameEnd + 32) free (UInt256.ofNat a.symbol.size) hin
    refine .inr ⟨hsource, hs', _, aw2, k2, C2, (hp free).trans hp2, ?_, r2⟩
    exact (stringReturnMemory_free mem1 (a.nameEnd + 32) free (UInt256.ofNat a.symbol.size)
      hin (by have hsz := hb1.size; omega)
      (by unfold ConstructorArgs.stringsEnd at hbelow; omega)).trans hf1

end Benchmarks.Morpho.MetaMorphoV1_1
