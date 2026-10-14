import Benchmarks.Morpho.MetaMorphoV1_1.MulticallIteration

/-! Inductive simulation of all multicall iterations with the same external-call semantics. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem multicallLoopSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {imms : Store} {results : List ByteArray}
    {mem rdata : ByteArray} {aw ptr : UInt256} {k C i : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 25 ≤ 1024)
    (hc : WordArrayCalldataChecks I.calldata) (hs : SourceState s0 I evm.accountMap evm)
    (hr : MulticallReady frame imms (multicallInput I.calldata) results i ptr)
    (hm : MulticallMemory mem ptr results) (hlen : results.length = calldataArrayLength I.calldata)
    (hdiff : calldataArrayLength I.calldata = i + remaining)
    (rd : RD (deployedRuntime v) I g s0 ⟨3877⟩
      (UInt256.ofNat i :: multicallInputBase I.calldata ::
        ((UInt256.ofNat I.calldata.size - multicallInputBase I.calldata) - ⟨31⟩) ::
        UInt256.ofNat (calldataArrayLength I.calldata) :: ⟨128⟩ :: R)
      mem aw rdata evm.accountMap k C) :
    (ExecForLoop config frame evm multicallLoopCondition multicallLoopPost multicallLoopBody
      .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (frame' : Frame) (mem' : ByteArray) (ptr' : UInt256) (results' : List ByteArray)
        (evm' : State) (rdata' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧
      MulticallReady frame' imms (multicallInput I.calldata) results'
        (calldataArrayLength I.calldata) ptr' ∧
      MulticallMemory mem' ptr' results' ∧ results'.length = calldataArrayLength I.calldata ∧
      ExecForLoop config frame evm multicallLoopCondition multicallLoopPost multicallLoopBody
        (.ok frame' evm') ∧
      RD (deployedRuntime v) I g s0 ⟨4003⟩
        (UInt256.ofNat (calldataArrayLength I.calldata) :: multicallInputBase I.calldata ::
          ((UInt256.ofNat I.calldata.size - multicallInputBase I.calldata) - ⟨31⟩) ::
          UInt256.ofNat (calldataArrayLength I.calldata) :: ⟨128⟩ :: R)
        mem' aw' rdata' evm'.accountMap k' C' := by
  have hn : calldataArrayLength I.calldata < UInt256.size := lt_of_le_of_lt hc.length (by decide)
  induction remaining generalizing evm frame results mem rdata aw ptr k C i with
  | zero =>
      have he : i = calldataArrayLength I.calldata := by omega
      subst i
      have hcond := multicallConditionSource (evm := evm) hr
      rw [multicallInput_length hc] at hcond
      simp only [Nat.lt_irrefl, decide_false] at hcond
      have r1 := metaMorphoV1_1_block_3877_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [ult_zero (le_refl _)]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact .inr ⟨frame, mem, ptr, results, evm, rdata, _, _, _, hs, hr, hm, hlen,
        ExecForLoop.falseDone hcond, r1⟩
  | succ n ih =>
      have hi : i < calldataArrayLength I.calldata := by omega
      have hcond := multicallConditionSource (evm := evm) hr
      rw [multicallInput_length hc] at hcond
      simp only [hi, decide_true] at hcond
      have r1 := metaMorphoV1_1_block_3877_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [ult_one (by rw [UInt256.toNat_ofNat_of_lt (show i < UInt256.size by omega),
              UInt256.toNat_ofNat_of_lt hn]; exact hi)]; rfl) rd
      rcases multicallIteration v hstack hc hs hr hm hlen hi r1 with
        ⟨hbad, hrev⟩ | ⟨evm', out, aw2, k2, C2, hs', hm', hbody, r2⟩
      · exact .inl ⟨ExecForLoop.bodyRevert hcond hbad, hrev⟩
      · let input := bytesTailData I.calldata
          (bytesArrayHead I.calldata (multicallInputBase I.calldata) i)
        have hr' := hr.stepFrame input out
        have hpost := multicallPostSource (evm := evm') hr' (by omega)
        rcases ih hs' (hr'.indexFrame (i + 1)) hm'
            (by rw [List.length_set]; exact hlen) (by omega) r2 with
          ⟨hbad, hrev⟩ | ⟨frame', mem', ptr', results', evm'', rdata', aw3, k3, C3,
            hs'', hr'', hm'', hlen', hloop, r3⟩
        · exact .inl ⟨ExecForLoop.iterate hcond hbody hpost hbad, hrev⟩
        · exact .inr ⟨frame', mem', ptr', results', evm'', rdata', aw3, k3, C3,
            hs'', hr'', hm'', hlen', ExecForLoop.iterate hcond hbody hpost hloop, r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
