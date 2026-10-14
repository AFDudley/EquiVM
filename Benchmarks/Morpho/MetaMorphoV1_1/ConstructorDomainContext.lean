import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainInit

/-! Arguments and the checked cursor available after domain initialization. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorInputFrame_preserves (a : ConstructorArgs) (cursors : List UInt256)
    (name : Ident) (hne : (cursorName == name) = false) :
    (constructorInputFrame a cursors).locals.get? name = (constructorFrame a).locals.get? name := by
  induction cursors with
  | nil => rfl
  | cons _ _ ih => rw [constructorInputFrame, store_get_ne _ _ hne]; exact ih

theorem constructorDomainReadyFrame_preserves (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) (name : Ident) (hc : (cursorName == name) = false)
    (hs : (slotsAndCursorName == name) = false) (hd : ("decimalResult" == name) = false)
    (hh : ("domain" == name) = false) :
    (constructorDomainReadyFrame a ok out I).locals.get? name = (constructorFrame a).locals.get? name := by
  rw [constructorDomainReadyFrame, constructorDomainCachedFrame, store_get_ne _ _ hh,
    constructorDomainReservedFrame, store_get_ne _ _ hc]
  have hp := cursorResultFrame_preserves (constructorReadyFrame a) "decimalResult" name
    (constructorDecimalsValue ok out) (constructorDecimalsCursor a out) hc hd hs
  have hbase := constructorInputFrame_preserves a
    [UInt256.ofNat (a.stringsEnd + 160), UInt256.ofNat (a.stringsEnd + 96),
      UInt256.ofNat (a.stringsEnd + 64), UInt256.ofNat (a.stringsEnd + 32),
      UInt256.ofNat a.stringsEnd, UInt256.ofNat a.nameEnd, UInt256.ofNat a.argumentEnd] name hc
  exact hp.trans hbase

theorem constructorDomainReadyFrame_contract (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) : (constructorDomainReadyFrame a ok out I).contract = contract := by
  simp only [constructorDomainReadyFrame, constructorDomainCachedFrame, constructorDomainReservedFrame,
    constructorDomainConstantsFrame, constructorAssetReadyFrame, constructorAssetFrame,
    constructorDecimalsReadyFrame, cursorResultFrame, constructorReadyFrame, constructorInputFrame_contract]

theorem constructorDomainReadyFrame_owner (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) :
    (constructorDomainReadyFrame a ok out I).locals.get? "owner" = some (.address a.owner) := by
  rw [constructorDomainReadyFrame_preserves a ok out I "owner" (by decide) (by decide) (by decide) (by decide)]
  exact constructorInputFrame_owner a []

theorem constructorDomainReadyFrame_morpho (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) :
    (constructorDomainReadyFrame a ok out I).locals.get? "morpho" = some (.address a.morpho) := by
  rw [constructorDomainReadyFrame_preserves a ok out I "morpho" (by decide) (by decide) (by decide) (by decide)]
  apply Std.HashMap.getElem?_ofList_of_mem (k := "morpho") (by decide)
  · simp
  · simp

theorem constructorDomainCachedMemory_free (mem : ByteArray) (I : ExecutionEnv) (free : Nat)
    (hlo : 96 ≤ free) :
    memLoad ⟨64⟩ (constructorDomainCachedMemory mem I free) = UInt256.ofNat (free + 192) := by
  have hm : 96 ≤ (constructorDomainAllocatedMemory mem I free).size := by
    have hb := packedWordsMemory_size (constructorDomainConstantsMemory mem) free
      (constructorDomainWords I) (by simp [constructorDomainWords])
    change 96 ≤ (packedWordsMemory _ _ _).size
    omega
  rw [constructorDomainCachedMemory,
    memLoad_writeWord_disjoint _ 256 ⟨64⟩ _
      (by rw [writeWord_sparse_size]; change 96 ≤ _; omega) (.inl (by decide)),
    memLoad_writeWord_disjoint _ 192 ⟨64⟩ _ hm (.inl (by decide)),
    constructorDomainAllocatedMemory_free]

end Benchmarks.Morpho.MetaMorphoV1_1
