import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayCalldata

/-! The reallocation ABI retains invalid rows until the loop accesses them. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

def reallocateCalldataValues (cd : ByteArray) (head : UInt256) : List Value :=
  (List.range (calldataWord cd head.toNat).toNat).map
    (retainedCalldataElement reallocateItemType reallocateCalldataPlan cd.toList
      (head + ⟨32⟩).toNat 192)

theorem reallocateCalldataValues_length (cd : ByteArray) (head : UInt256) :
    (reallocateCalldataValues cd head).length = (calldataWord cd head.toNat).toNat := by
  simp only [reallocateCalldataValues, List.length_map, List.length_range]

theorem reallocateCalldataValues_getElem (cd : ByteArray) (head : UInt256) (i : Nat)
    (hi : i < (calldataWord cd head.toNat).toNat) :
    (reallocateCalldataValues cd head)[i]? =
      some (retainedCalldataElement reallocateItemType reallocateCalldataPlan cd.toList
        (head + ⟨32⟩).toNat 192 i) := by
  rw [List.getElem?_eq_getElem (by rwa [reallocateCalldataValues_length])]
  simp only [reallocateCalldataValues, List.getElem_map, List.getElem_range]

theorem decodeReallocateArrayValue (cd : ByteArray) (head : UInt256) :
    decodeValue? (.dynamicArray reallocateItemType) cd.toList head.toNat
        reallocateCalldataPlan false =
      if solcMaxU64 < (calldataWord cd head.toNat).toNat ||
          badExtent false false cd.toList head.toNat
            (calldataWord cd head.toNat).toNat 192 then none
      else some (.array (reallocateCalldataValues cd head)) := by
  rw [decodeRetainedArrayValue (by rfl) (by rfl) (by decide), solcReadNat_word_total,
    show isMemory reallocateCalldataPlan = false from rfl]
  have h32 : solcAdd head.toNat 32 = (head + ⟨32⟩).toNat := solcAdd_word head ⟨32⟩
  simp only [reallocateCalldataValues, h32]

open Classical in
theorem decodeReallocateCalldataRaw {cd : ByteArray} (name : Ident)
    (table : List (Nat × List CalldataPlan)) (h4 : 4 ≤ cd.size)
    (hplans : ((table.find? (fun entry ↦ entry.1 ==
      (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] =
        [reallocateCalldataPlan]) :
    decodeCalldataWithMode (.solc08Calldata table) [name]
        [.dynamicArray reallocateItemType] cd =
      if solcSLT (solcSub cd.size 4) 32 then none
      else if solcMaxU64 < (calldataWord cd 4).toNat then none
      else if solcMaxU64 < (calldataWord cd (⟨4⟩ + calldataWord cd 4).toNat).toNat ||
          badExtent false false cd.toList (⟨4⟩ + calldataWord cd 4).toNat
            (calldataWord cd (⟨4⟩ + calldataWord cd 4).toNat).toNat 192 then none
      else some ((∅ : Store).insert name
        (.array (reallocateCalldataValues cd (⟨4⟩ + calldataWord cd 4)))) := by
  rw [decodeCalldataSolc08, if_neg (by omega : ¬ cd.size < 4)]
  simp only [decodeArgs?, List.isEmpty_cons, Bool.false_eq_true, if_false,
    show abiTupleHeadSize? [.dynamicArray reallocateItemType] = some 32 from by
      simp only [abiTupleHeadSize?, isDynamicABIType, bind, Option.bind, if_true, Nat.add_zero],
    bind, Option.bind]
  by_cases hh : solcSLT (solcSub cd.size 4) 32 = true
  · simp only [hh, if_true]
  simp only [hh, hplans]
  simp only [decodeFields?, stride?, isDynamicABIType, if_true, List.headD_cons,
    retainFailure, show reallocateCalldataPlan.deferErrors.contains [] = false from rfl,
    Bool.false_eq_true, if_false, solcTailTarget?, Bool.not_true,
    show solcAdd 4 0 = 4 from rfl, bind, Option.bind, Bool.and_false]
  have hr : solcReadNat cd.toList 4 = (calldataWord cd 4).toNat :=
    solcReadNat_word_total cd ⟨4⟩
  have hp : solcAdd 4 (calldataWord cd 4).toNat = (⟨4⟩ + calldataWord cd 4).toNat :=
    solcAdd_word ⟨4⟩ (calldataWord cd 4)
  rw [hr]
  by_cases ho : solcMaxU64 < (calldataWord cd 4).toNat
  · simp only [ho, if_true]
  simp only [ho, if_false, hp]
  rw [decodeReallocateArrayValue]
  split_ifs <;> rfl

end Benchmarks.Morpho.MetaMorphoV1_1
