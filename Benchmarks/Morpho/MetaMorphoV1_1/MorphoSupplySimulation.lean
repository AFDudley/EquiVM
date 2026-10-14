import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSupplyEncode
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSupplyReturn
import Benchmarks.Morpho.MetaMorphoV1_1.ZeroCallSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.BoundedCallMemory

/-! Same-call correspondence for Morpho supply, including the caught revert and decoding failures. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem morphoSupplyReturnSize {evm evm' : State} {target sender : AccountAddress}
    {p : MarketParamsData} {amount : UInt256} {out : ByteArray} {ok : Bool}
    (hcall : typedCallViaEVM config evm target "supply" 0
      [p.value, uint256Value amount, uint256Value ⟨0⟩, .address sender, .bytes ByteArray.empty]
      (ok, evm', out)) : out.size < 2 ^ 138 := by
  obtain ⟨input, he, hcall⟩ := hcall
  rw [morphoSupplyEncode, Option.some.injEq] at he
  subst input
  exact callViaEVM_output_bound hcall (by rw [morphoSupplyCalldata_size]; decide +kernel)

set_option maxRecDepth 2000 in
theorem morphoSupplySimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params amount i morpho assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 20 ≤ 1024)
    (hs : SourceState s0 I σ evm)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hparamslo : 96 ≤ params.toNat) (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params p)
    (hsub : amount.toNat ≤ assets.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨18186⟩
      (params :: amount :: i :: morpho :: assets :: R) mem aw rdata σ k C) :
    (∃ evm' out, typedCallViaEVM config evm (AccountAddress.ofUInt256 morpho) "supply" 0
      [p.value, uint256Value amount, uint256Value ⟨0⟩, .address I.codeOwner, .bytes ByteArray.empty]
      (true, evm', out) ∧ out.size < 2 ^ 255 ∧
      ¬ (64 ≤ out.size ∧ allocationFits ptr ⟨64⟩) ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (ok : Bool) (out mem' : ByteArray) (cursor aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm (AccountAddress.ofUInt256 morpho) "supply" 0
        [p.value, uint256Value amount, uint256Value ⟨0⟩, .address I.codeOwner, .bytes ByteArray.empty]
        (ok, evm', out) ∧ SourceState s0 I evm'.accountMap evm' ∧ out.size < 2 ^ 255 ∧
      (ok = true → 64 ≤ out.size ∧ allocationFits ptr ⟨64⟩) ∧
      cursor = (if ok then nextCursor ptr ⟨64⟩ else ptr) ∧
      memLoad ⟨64⟩ mem' = cursor ∧ cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧
      MemoryPrefix mem mem' ptr.toNat ∧
      RD (deployedRuntime v) I g s0 ⟨18168⟩
        ((if ok then ⟨0⟩ else amount) :: (if ok then ⟨0⟩ else amount) :: i :: morpho ::
          (if ok then UInt256.sub assets amount else assets) :: R)
        mem' aw' out evm'.accountMap k' C' := by
  obtain ⟨gasArg, aw1, k1, C1, h1⟩ := morphoSupplyReachCall v p hstack hfree hptr
    hparamslo hparams hmem hloads rd
  have hdec : decode (deployedRuntime v) ⟨18226⟩ = some (.CALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨18226⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
      immutableLayout_inBounds, immutableTemplate_size64)
  obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', hout, h2⟩ :=
    typedZeroCallSimulation (by simp only [List.length_cons]; omega) hdec hs rfl
      (by change _ = some ((morphoSupplyCallMem mem ptr.toNat p amount I.codeOwner).readWithPadding
          ptr.toNat 324)
          rw [morphoSupplyEncode, morphoSupplyCallMem_read]) h1
  have hhi : out.size < 2 ^ 255 := lt_trans (morphoSupplyReturnSize hcall) (by decide)
  have hinput : ptr.toNat ≤ (morphoSupplyCallMem mem ptr.toNat p amount I.codeOwner).size := by
    rw [morphoSupplyCallMem_size]; omega
  have hprefix := (wordCallMemory_prefix mem ptr.toNat morphoSupplySelectorWord
    (morphoSupplyWords p amount I.codeOwner)).trans
      (fixedReturnBuffer_prefix (cap := 64) (by decide) hout hinput)
  have hf : memLoad ⟨64⟩ (fixedReturnBuffer
      (morphoSupplyCallMem mem ptr.toNat p amount I.codeOwner) ptr out 64) = ptr := by
    rw [fixedReturnBuffer_free (by decide) hout hinput (by omega), morphoSupplyCallMem,
      wordCallMemory_free _ _ (by omega) (by omega), hfree]
  cases ok with
  | false =>
      obtain ⟨aw3, k3, C3, h3⟩ := morphoSupplyCaughtFailure v (by omega) h2
      exact .inr ⟨evm', false, out, _, ptr, aw3, k3, C3, hcall, hs', hhi,
        by simp, rfl, hf, hptr, le_refl _, hprefix, h3⟩
  | true =>
      by_cases hgood : 64 ≤ out.size ∧ allocationFits ptr ⟨64⟩
      · obtain ⟨aw3, k3, C3, h3⟩ := morphoSupplySuccessfulReturn v (by omega) hout
          hgood.1 hgood.2 hsub h2
        exact .inr ⟨evm', true, out, _, nextCursor ptr ⟨64⟩, aw3, k3, C3,
          hcall, hs', hhi, fun _ ↦ hgood, rfl, memLoad_write_same _ _ _ _ rfl,
          hgood.2.1, hgood.2.2,
          hprefix.trans (memoryPrefix_sparse_writeWord _ 64 _ _ (.inr (by decide))), h3⟩
      · exact .inl ⟨evm', out, hcall, hhi, hgood,
          morphoSupplyReturnReverts v (by simp only [List.length_cons]; omega) hout hgood h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
