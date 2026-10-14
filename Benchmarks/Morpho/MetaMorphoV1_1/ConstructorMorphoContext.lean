import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorMorphoSource

/-! Constructor arguments and the cursor after the MORPHO immutable assignment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] ConstructorArgs.encoded
set_option autoImplicit false

def constructorMorphoReadyFrame (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) : Frame :=
  constructorMorphoFrame (constructorTimelockReadyFrame a ok out I) a.morpho

theorem constructorMorphoReadyFrame_contract (a : ConstructorArgs) (ok : Bool)
    (out : ByteArray) (I : ExecutionEnv) :
    (constructorMorphoReadyFrame a ok out I).contract = contract :=
  constructorTimelockReadyFrame_contract a ok out I

theorem constructorMorphoReadyFrame_asset (a : ConstructorArgs) (ok : Bool)
    (out : ByteArray) (I : ExecutionEnv) :
    (constructorMorphoReadyFrame a ok out I).locals.get? "assetAddress" = some (.address a.asset) := by
  change (constructorTimelockReadyFrame a ok out I).locals.get? "assetAddress" = _
  rw [constructorTimelockReadyFrame_preserves a ok out I "assetAddress"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact constructorInputFrame_asset a []

theorem constructorMorphoReadyFrame_cursor (a : ConstructorArgs) (ok : Bool)
    (out : ByteArray) (I : ExecutionEnv) :
    (constructorMorphoReadyFrame a ok out I).locals.get? cursorName =
      some (uint256Value (UInt256.ofNat ((constructorDecimalsCursor a out).toNat + 192))) := by
  have hn : nextCursor (constructorDecimalsCursor a out) ⟨192⟩ =
      UInt256.ofNat ((constructorDecimalsCursor a out).toNat + 192) := by
    rw [← ofNat_add_words, u256_ofNat_toNat]
    rfl
  have hd : (constructorDomainReadyFrame a ok out I).locals.get? cursorName =
      some (uint256Value (UInt256.ofNat ((constructorDecimalsCursor a out).toNat + 192))) := by
    rw [constructorDomainReadyFrame, constructorDomainCachedFrame, store_get_ne _ _ (by decide),
      constructorDomainReservedFrame, store_get_self, hn]
  have ho : (constructorOwnershipFrame (constructorDomainReadyFrame a ok out I)).locals.get? cursorName =
      some (uint256Value (UInt256.ofNat ((constructorDecimalsCursor a out).toNat + 192))) := by
    rw [constructorOwnershipFrame, store_get_ne _ _ (by decide)]
    exact hd
  rw [constructorMorphoReadyFrame, constructorMorphoFrame, constructorTimelockReadyFrame,
    constructorSetTimelockFrame, store_get_ne _ _ (by decide)]
  unfold constructorTimelockCheckedFrame
  split
  · exact ho
  · rw [store_get_ne _ _ (by decide)]; exact ho

end Benchmarks.Morpho.MetaMorphoV1_1
