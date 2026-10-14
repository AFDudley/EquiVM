import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorApproveInit

/-! The immutable store produced by a successful constructor and its deployment words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] constructorNameHash constructorVersionHash constructorDomainHash
set_option autoImplicit false
set_option maxRecDepth 2000

def constructorFinalImms (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) (strictOut : ByteArray) : Store :=
  (((((((((((initialImmutables contract).insert
    "_underlyingDecimals" (uint256Value (constructorUnderlyingDecimals ok out))).insert
    "_asset" (.address a.asset)).insert "_name" (uint256Value ⟨0⟩)).insert
    "_version" (uint256Value constructorVersionWord)).insert
    "_hashedName" (uint256Value constructorNameHash)).insert
    "_hashedVersion" (uint256Value constructorVersionHash)).insert
    "_cachedChainId" (uint256Value (UInt256.ofNat Ethereum.chainId))).insert
    "_cachedDomainSeparator" (uint256Value (constructorDomainHash I))).insert
    "_cachedThis" (.address I.codeOwner)).insert
    "MORPHO" (.address a.morpho)).insert
    "DECIMALS_OFFSET" (uint256Value (constructorDecimalsOffset (calldataWord strictOut 0)))

def constructorImmutableValues (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) (strictOut : ByteArray) : List UInt256 :=
  [UInt256.ofNat a.asset.val, constructorUnderlyingDecimals ok out,
    constructorDomainHash I, UInt256.ofNat Ethereum.chainId, UInt256.ofNat I.codeOwner.val,
    constructorNameHash, constructorVersionHash, ⟨0⟩, constructorVersionWord,
    UInt256.ofNat a.morpho.val, constructorDecimalsOffset (calldataWord strictOut 0)]

theorem constructorTimelockCheckedFrame_immutables (frame : Frame) (value : UInt256) :
    (constructorTimelockCheckedFrame frame value).immutables = frame.immutables := by
  unfold constructorTimelockCheckedFrame
  split <;> rfl

theorem constructorFinalFrame_immutables (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) (strictOut : ByteArray) (cursor : UInt256) :
    (constructorFinalFrame a ok out I strictOut cursor).immutables =
      constructorFinalImms a ok out I strictOut := by
  simp only [constructorFinalFrame, cursorResultFrame, constructorOffsetFrame,
    constructorFinalDecimalsFrame, constructorStrictDecimalsFrame, constructorMorphoReadyFrame,
    constructorMorphoFrame, constructorTimelockReadyFrame, constructorSetTimelockFrame,
    constructorTimelockCheckedFrame_immutables, constructorOwnershipFrame,
    constructorDomainReadyFrame, constructorDomainCachedFrame, constructorDomainReservedFrame,
    constructorDomainConstantsFrame, constructorAssetReadyFrame, constructorAssetFrame,
    constructorDecimalsReadyFrame, constructorReadyFrame, constructorInputFrame, constructorFrame,
    constructorFinalImms]

theorem constructorFinalImms_word (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) (strictOut : ByteArray) {i : Nat} (hi : i < 11) :
    wordsOf (constructorFinalImms a ok out I strictOut)
      ((immutableReferences.map Prod.fst).getD i "") =
      (constructorImmutableValues a ok out I strictOut).getD i ⟨0⟩ := by
  interval_cases i <;>
    simp only [immutableReferences, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, wordsOf, constructorFinalImms, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, String.reduceBEq, Bool.false_eq_true, ite_false, ite_true,
      valueToWord, uint256Value, wordOfInt_ofNat_toNat_gen, constructorImmutableValues,
      Option.bind_some, Option.getD_some, pure, u256_ofNat_toNat] <;> rfl

theorem constructorFinalImms_fit (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) (strictOut : ByteArray) :
    immutablesFit contract (constructorFinalImms a ok out I strictOut) := by
  have hu := constructorUnderlyingDecimals_bound ok out
  have hd := constructorDecimalsOffset_bound (calldataWord strictOut 0)
  have hdomain := (constructorDomainHash I).val.isLt
  have hchain := (UInt256.ofNat Ethereum.chainId).val.isLt
  have hname := constructorNameHash.val.isLt
  have hversion := constructorVersionHash.val.isLt
  have hver := constructorVersionWord.val.isLt
  intro d hdcl
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hdcl
  change i < 11 at hi
  interval_cases i <;>
    dsimp only [contract, Syntax.contractSyntax, List.getElem_cons_zero, List.getElem_cons_succ] <;>
    simp only [constructorFinalImms, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      String.reduceBEq, Bool.false_eq_true, ite_false, ite_true, Option.some.injEq] <;>
    refine ⟨_, rfl, ?_⟩ <;>
    simp only [elemValueFits, decide_eq_true_eq, Int.ofNat_eq_natCast] <;>
    refine ⟨Int.natCast_nonneg _, ?_⟩
  case «1» => exact Int.ofNat_lt.mpr hu
  case «2» => exact Int.ofNat_lt.mpr hdomain
  case «3» => exact Int.ofNat_lt.mpr hchain
  case «5» => exact Int.ofNat_lt.mpr hname
  case «6» => exact Int.ofNat_lt.mpr hversion
  case «7» => exact Int.ofNat_lt.mpr (show (0 : Nat) < UInt256.size by decide)
  case «8» => exact Int.ofNat_lt.mpr hver
  case «10» => exact Int.ofNat_lt.mpr hd

end Benchmarks.Morpho.MetaMorphoV1_1
