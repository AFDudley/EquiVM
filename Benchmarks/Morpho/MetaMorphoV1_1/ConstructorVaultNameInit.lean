import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultAssignInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultStringBuffers

/-! Initialize the vault name while preserving the symbol buffer and the checked free pointer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorVaultNameInit {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ok : Bool) (out : ByteArray) (hs : SourceState s0 I σ evm)
    (hperm : I.perm = true) (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (hcursor : a.stringsEnd ≤ (constructorDecimalsCursor a out).toNat)
    (hn : BytesBuffer (constructorTimelockMemory mem a ok out I) (UInt256.ofNat a.argumentEnd) a.name)
    (hv : BytesBuffer (constructorTimelockMemory mem a ok out I) (UInt256.ofNat a.nameEnd) a.symbol)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨780⟩
      (constructorVaultNameTail a) (constructorTimelockMemory mem a ok out I) aw rdata σ k C) :
    (ExecBlock config (constructorTimelockReadyFrame a ok out I) evm (contract.ctor.body.drop 29) .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) g s0) ∨
    ((∀ result, ExecBlock config (constructorTimelockReadyFrame a ok out I)
        (storageStringWriteState evm ⟨24⟩ a.name) (contract.ctor.body.drop 30) result →
      ExecBlock config (constructorTimelockReadyFrame a ok out I) evm (contract.ctor.body.drop 29) result) ∧
      SourceState s0 I (storageStringWriteState evm ⟨24⟩ a.name).accountMap
        (storageStringWriteState evm ⟨24⟩ a.name) ∧
      ∃ mem' aw' k' C', StringBuffer mem' a.argumentEnd a.name ∧
        StringBuffer mem' a.nameEnd a.symbol ∧
        (∀ limit, ByteMemoryPrefix (constructorTimelockMemory mem a ok out I) mem' limit) ∧
        memLoad ⟨64⟩ mem' = UInt256.ofNat ((constructorDecimalsCursor a out).toNat + 192) ∧
        RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨874⟩
          (UInt256.ofNat a.argumentEnd :: ⟨885⟩ :: stringSetTopic false :: constructorVaultTail a false)
          mem' aw' rdata (storageStringWriteState evm ⟨24⟩ a.name).accountMap k' C') := by
  obtain ⟨hnb, hvb⟩ := constructorTimelockMemory_stringBuffers a ok out I hsmall hname hcursor hn hv
  have hnfit : a.argumentEnd < UInt256.size := by change a.argumentEnd < 2 ^ 256; omega
  have hvfit : a.nameEnd < UInt256.size := by change a.nameEnd < 2 ^ 256; omega
  have hnptr := UInt256.toNat_ofNat_of_lt hnfit
  have hnlo : 96 ≤ a.argumentEnd := by unfold ConstructorArgs.argumentEnd; omega
  have hvlo : 96 ≤ a.nameEnd := by unfold ConstructorArgs.nameEnd; omega
  have hnpad : a.name.size ≤ paddedSize a.name.size := by unfold paddedSize; omega
  have hnf : (UInt256.ofNat a.argumentEnd).toNat + 32 + a.name.size < UInt256.size := by
    rw [hnptr]
    unfold ConstructorArgs.nameEnd at hvfit
    omega
  rcases constructorVaultAssignInit (frame := constructorTimelockReadyFrame a ok out I)
      a false hs hperm (constructorTimelockReadyFrame_contract a ok out I)
      (constructorTimelockReadyFrame_string a ok out I false)
      (constructorTimelockReadyFrame_unshadowed a ok out I false)
      (by simpa only [hnptr] using hnb) (by rw [hnptr]; exact hnlo)
      hnf (a.string_sizes_small hsmall).1 rd with hfail | hsuccess
  · exact .inl hfail
  · obtain ⟨hsource, hs', mem', aw', k', C', hnb', hp, hf, rd'⟩ := hsuccess
    refine .inr ⟨hsource, hs', mem', aw', k', C', ?_, ?_, hp, ?_, rd'⟩
    · simpa only [hnptr] using hnb'
    · exact hvb.preserve (hp (constructorTimelockMemory mem a ok out I).size).words
        hvlo hvfit hvb.size
    · exact hf.trans (constructorTimelockMemory_free mem a ok out I (by
        unfold ConstructorArgs.stringsEnd ConstructorArgs.nameEnd at hcursor
        omega))

end Benchmarks.Morpho.MetaMorphoV1_1
