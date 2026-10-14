import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorApproveSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorFinalMemory

/-! Couple the constructor's final immutable assignment and approval call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorFinalFrame (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) (strictOut : ByteArray) (cursor : UInt256) : Frame :=
  cursorResultFrame
    (constructorOffsetFrame (constructorFinalDecimalsFrame a ok out I strictOut) (calldataWord strictOut 0))
    "approveMorpho" (.tuple []) cursor

theorem constructorApproveInit {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ok : Bool) (out strictOut : ByteArray)
    (hmem : 128 ≤ mem.size) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hlo : 480 ≤ (constructorStrictDecimalsPtr a out).toNat)
    (halloc : allocationFits (constructorStrictDecimalsPtr a out) ⟨32⟩)
    (hd : (calldataWord strictOut 0).toNat < 256)
    (hfree : memLoad ⟨64⟩ mem = nextCursor (constructorStrictDecimalsPtr a out) ⟨32⟩)
    (hs : SourceState s0 I σ evm)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1053⟩
      [⟨255⟩, calldataWord strictOut 0, UInt256.ofNat a.asset.val,
        UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩] mem aw strictOut σ k C) :
    (ExecBlock config (constructorFinalDecimalsFrame a ok out I strictOut) evm
        (contract.ctor.body.drop 36) .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    ∃ (evm' : State) (mem' result : ByteArray) (cursor aw' x0 x1 x2 x3 : UInt256) (k' C' : Nat),
      ExecBlock config (constructorFinalDecimalsFrame a ok out I strictOut) evm
        (contract.ctor.body.drop 36) (.ok (constructorFinalFrame a ok out I strictOut cursor) evm') ∧
      SourceState s0 I evm'.accountMap evm' ∧
      ByteMemoryPrefix (writeWord mem 448 (constructorDecimalsOffset (calldataWord strictOut 0))) mem' 480 ∧
      memLoad ⟨64⟩ mem' = cursor ∧ cursor.toNat < 2 ^ 64 ∧ 480 ≤ cursor.toNat ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1153⟩
        [x0, x1, x2, x3, ⟨64⟩] mem' aw' result evm'.accountMap k' C' := by
  let frame := constructorOffsetFrame (constructorFinalDecimalsFrame a ok out I strictOut)
    (calldataWord strictOut 0)
  have hc : frame.contract = contract := constructorFinalDecimalsFrame_contract a ok out I strictOut
  have ha : frame.locals.get? "assetAddress" = some (.address a.asset) :=
    constructorFinalDecimalsFrame_asset a ok out I strictOut
  have hm : frame.locals.get? "morpho" = some (.address a.morpho) :=
    constructorFinalDecimalsFrame_morpho a ok out I strictOut
  have hp : frame.locals.get? cursorName =
      some (uint256Value (nextCursor (constructorStrictDecimalsPtr a out) ⟨32⟩)) :=
    constructorFinalDecimalsFrame_cursor a ok out I strictOut
  have hnext : 480 ≤ (nextCursor (constructorStrictDecimalsPtr a out) ⟨32⟩).toNat :=
    le_trans hlo halloc.2
  rcases constructorForceApprove a frame.immutables hmem hnext halloc.1 hd hfree hzero hs rd with
    hbad | hgood
  · refine .inl ⟨?_, hbad.2⟩
    exact constructorDecimalsOffsetPrefix
      (constructorFinalDecimalsFrame_contract a ok out I strictOut)
      (constructorFinalDecimalsFrame_decimals a ok out I strictOut)
      (constructorApprovalReverts hc ha hm hp hbad.1)
  · obtain ⟨evm', frame', mem', result, cursor, aw', x0, x1, x2, x3, k', C',
      hbody, hs', hprefix, hfree', hbound, hmono, rd'⟩ := hgood
    refine .inr ⟨evm', mem', result, cursor, aw', x0, x1, x2, x3, k', C', ?_,
      hs', hprefix.mono hnext, hfree', hbound, le_trans hnext hmono, rd'⟩
    exact constructorDecimalsOffsetPrefix
      (constructorFinalDecimalsFrame_contract a ok out I strictOut)
      (constructorFinalDecimalsFrame_decimals a ok out I strictOut)
      (constructorApprovalReturns hc ha hm hp hbody)

end Benchmarks.Morpho.MetaMorphoV1_1
