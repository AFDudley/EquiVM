import Benchmarks.Morpho.MetaMorphoV1_1.MulticallInput
import Benchmarks.Morpho.MetaMorphoV1_1.MulticallCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.MulticallStepMemory
import Benchmarks.Morpho.MetaMorphoV1_1.MulticallDelegateSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.MulticallStoreRuntime

/-! One complete multicall iteration, including source and runtime failure paths. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

theorem multicallIteration {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {imms : Store} {results : List ByteArray}
    {mem rdata : ByteArray} {aw ptr : UInt256} {k C i : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 25 ≤ 1024)
    (hc : WordArrayCalldataChecks I.calldata) (hs : SourceState s0 I evm.accountMap evm)
    (hr : MulticallReady frame imms (multicallInput I.calldata) results i ptr)
    (hm : MulticallMemory mem ptr results) (hlen : results.length = calldataArrayLength I.calldata)
    (hi : i < calldataArrayLength I.calldata)
    (rd : RD (deployedRuntime v) I g s0 ⟨3886⟩
      (UInt256.ofNat i :: multicallInputBase I.calldata ::
        ((UInt256.ofNat I.calldata.size - multicallInputBase I.calldata) - ⟨31⟩) ::
        UInt256.ofNat (calldataArrayLength I.calldata) :: ⟨128⟩ :: R)
      mem aw rdata evm.accountMap k C) :
    let input := bytesTailData I.calldata (bytesArrayHead I.calldata (multicallInputBase I.calldata) i)
    let copied := multicallElementMemory mem I.calldata ptr (multicallInputBase I.calldata) i
    let cp := bytesAllocPtr ptr input.size
    (ExecBlock config frame evm multicallLoopBody .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧
      MulticallMemory (multicallStoreResultMemory copied cp out i)
        (callReturnCursor cp out) (results.set i out) ∧
      ExecBlock config frame evm multicallLoopBody
        (.ok (multicallStepFrame frame input ptr out results i) evm') ∧
      RD (deployedRuntime v) I g s0 ⟨3877⟩
        (UInt256.ofNat (i + 1) :: multicallInputBase I.calldata ::
          ((UInt256.ofNat I.calldata.size - multicallInputBase I.calldata) - ⟨31⟩) ::
          UInt256.ofNat (calldataArrayLength I.calldata) :: ⟨128⟩ :: R)
        (multicallStoreResultMemory copied cp out i) aw' out evm'.accountMap k' C' := by
  dsimp only
  let base := multicallInputBase I.calldata
  let input := bytesTailData I.calldata (bytesArrayHead I.calldata base i)
  let copied := multicallElementMemory mem I.calldata ptr base i
  let cp := bytesAllocPtr ptr input.size
  have hget := multicallInput_getElem hc i hi
  have hiw : 32 * i < UInt256.size := by
    have hn := hc.length
    change calldataArrayLength I.calldata ≤ 18446744073709551615 at hn
    change _ < 2 ^ 256
    omega
  have hsize (ha : bytesArrayAccessValid I.calldata base i) : input.size < 2 ^ 64 := by
    dsimp only [input]
    rw [bytesTailData_size]
    have hl := ha.2.1
    change _ ≤ 18446744073709551615 at hl
    omega
  rcases multicallElementCopy v (by simp only [List.length_cons]; omega)
      hiw hc.size hm.free rd with ⟨hbad, hrev⟩ | ⟨ha, hf, aw1, k1, C1, r1⟩
  · by_cases ha : bytesArrayAccessValid I.calldata base i
    · rw [if_pos ha] at hget
      exact .inl ⟨multicallCopyReverts hr hget (hsize ha)
        (hbad.resolve_left (not_not_intro ha)), hrev⟩
    · rw [if_neg ha] at hget
      exact .inl ⟨multicallReadReverts hr hget, hrev⟩
  have hl := hsize ha
  rw [if_pos ha] at hget
  have hm1 := hm.copy hc.size ha hf
  change MulticallMemory copied cp results at hm1
  have hbuf := multicallElementMemory_buffer (mem := mem) hm.bound
    (by have := hm.lower; omega) hc.size ha
  rcases multicallDelegateSimulation v imms (by simp only [List.length_cons]; omega)
      hm1.bound (by have := hm.bound; change _ < 2 ^ 256; omega) hm1.free hm1.zero
      hbuf (lt_trans hl (by decide)) hs
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1 with
    ⟨hb, hrev⟩ | ⟨evm', out, aw2, k2, C2, hs', hfit, hb, r2⟩
  · have hbody := multicallDelegateReverts (evm := evm) hr hget hl hf
      (by simpa only [hs.env] using hb)
    exact .inl ⟨hbody, hrev⟩
  have hm2 := hm1.preserve (callReturnMemory_bytePrefix copied cp out)
    (callReturnCursor_bound cp out hm1.bound hfit).1
    (callReturnCursor_bound cp out hm1.bound hfit).2
    (callReturnMemory_free copied cp out (by have := hm1.lower; omega) hm1.free)
  have hbody := multicallDelegateReturns (evm := evm) (evm' := evm') hr hget hl hf
    (by omega) (by simpa only [hs.env] using hb)
  have harray : 160 + 32 * calldataArrayLength I.calldata < UInt256.size := by
    have hlo := hm2.lower
    have hhi := hm2.bound
    rw [hlen] at hlo
    change _ < 2 ^ 256
    omega
  obtain ⟨aw3, k3, C3, r3⟩ := multicallStoreResult v (by omega) hi
    harray
    (by have := hm2.size; omega) (by rw [← hlen]; exact hm2.length) r2
  exact .inr ⟨evm', out, aw3, k3, C3, hs', hm1.storeReturn (by omega) hfit, hbody, r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
