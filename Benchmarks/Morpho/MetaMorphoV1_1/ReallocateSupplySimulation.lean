import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSupplyEncode
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSupplyReturn
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSupplySimulation

/-! Same-call correspondence for the strict supply performed by reallocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem reallocateSupplySimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params allocation amount id x : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 19 ≤ 1024)
    (hs : SourceState s0 I σ evm)
    (halloc : memLoad allocation mem = params)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hparamslo : 96 ≤ params.toNat) (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params p)
    (rd : RD (deployedRuntime v) I g s0 ⟨6526⟩
      (allocation :: id :: amount :: x :: R) mem aw rdata σ k C) :
    (∃ evm' ok out, typedCallViaEVM config evm v.MORPHO "supply" 0
      [p.value, uint256Value amount, uint256Value ⟨0⟩, .address I.codeOwner, .bytes ByteArray.empty]
      (ok, evm', out) ∧ out.size < 2 ^ 255 ∧
      (ok = false ∨ ¬ (64 ≤ out.size ∧ allocationFits ptr ⟨64⟩)) ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (out mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm v.MORPHO "supply" 0
        [p.value, uint256Value amount, uint256Value ⟨0⟩, .address I.codeOwner, .bytes ByteArray.empty]
        (true, evm', out) ∧ SourceState s0 I evm'.accountMap evm' ∧ out.size < 2 ^ 255 ∧
      64 ≤ out.size ∧ allocationFits ptr ⟨64⟩ ∧
      memLoad ⟨64⟩ mem' = nextCursor ptr ⟨64⟩ ∧ MemoryPrefix mem mem' ptr.toNat ∧
      RD (deployedRuntime v) I g s0 ⟨6716⟩
        (calldataWord out 32 :: calldataWord out 0 :: x :: id :: amount :: ⟨6686⟩ :: ⟨1⟩ :: R)
        mem' aw' out evm'.accountMap k' C' := by
  obtain ⟨gasArg, aw1, k1, C1, h1⟩ := reallocateSupplyReachCall v p
    (by simp only [List.length_cons]; omega) halloc hfree hptr hparamslo hparams hmem hloads rd
  have hdec : decode (deployedRuntime v) ⟨6609⟩ = some (.CALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨6609⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
      immutableLayout_inBounds, immutableTemplate_size64)
  obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', hout, h2⟩ :=
    typedZeroCallSimulation (address := v.MORPHO)
      (by simp only [List.length_cons]; omega) hdec hs (by
        rw [accountAddress_ofUInt256_eq_ofNat_toNat]
        exact (accountAddress_of_word_val _).symm)
      (by change _ = some ((morphoSupplyCallMem mem ptr.toNat p amount I.codeOwner).readWithPadding
          ptr.toNat 324)
          rw [morphoSupplyEncode, morphoSupplyCallMem_read]) h1
  have hhi : out.size < 2 ^ 255 := lt_trans (morphoSupplyReturnSize hcall) (by decide)
  cases ok with
  | false =>
      exact .inl ⟨evm', false, out, hcall, hhi, .inl rfl,
        reallocateSupplyCallFailure v (by omega) hout h2⟩
  | true =>
      rcases reallocateSupplyReturnAllocation v (by omega) hout h2 with
        ⟨hbad, hrev⟩ | ⟨hlong, hfit, aw3, k3, C3, h3⟩
      · exact .inl ⟨evm', true, out, hcall, hhi, .inr hbad, hrev⟩
      · have hinput : ptr.toNat ≤
            (morphoSupplyCallMem mem ptr.toNat p amount I.codeOwner).size := by
          rw [morphoSupplyCallMem_size]; omega
        have hword : ptr.toNat + 64 < UInt256.size := by change _ < 2 ^ 256; omega
        have hsize := fixedReturnBuffer_size (by decide : 0 < 64) hinput hlong hout
        have hload (off : Nat) (hoff : off + 32 ≤ 64) :
            memLoad (ptr + UInt256.ofNat off)
              (writeWord (fixedReturnBuffer
                (morphoSupplyCallMem mem ptr.toNat p amount I.codeOwner) ptr out 64)
                64 (nextCursor ptr ⟨64⟩)) = calldataWord out off := by
          rw [wordWindowRead_freeWrite (len := 64) _ (by omega) (by omega) hword hoff]
          exact fixedReturnBuffer_load hinput hlong hout hword hoff
        have hload0 := hload 0 (by decide)
        rw [show ptr + UInt256.ofNat 0 = ptr from u256_add_zero ptr] at hload0
        simp only [fixedReturnBuffer, show UInt256.ofNat 64 = (⟨64⟩ : UInt256) from rfl]
          at hload hload0
        rw [hload 32 (by decide), hload0] at h3
        have hprefix := (wordCallMemory_prefix mem ptr.toNat morphoSupplySelectorWord
          (morphoSupplyWords p amount I.codeOwner)).trans
            (fixedReturnBuffer_prefix (cap := 64) (by decide) hout hinput)
        exact .inr ⟨evm', out, _, aw3, k3, C3, hcall, hs', hhi, hlong, hfit,
          memLoad_write_same _ _ _ _ rfl,
          hprefix.trans (memoryPrefix_sparse_writeWord _ 64 _ _ (.inr (by decide))), h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
