import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayHead

/-! Entry decoding for multicall, including every malformed outer calldata header. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
open Benchmarks.EAS.Attester (ArrayHeadChecks arrayHead)

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

open Classical in
theorem decodeCalldataBytesArrayRaw {cd : ByteArray} (name : Ident)
    (table : List (Nat × List CalldataPlan)) (h4 : 4 ≤ cd.size)
    (hplans : ((table.find? (fun entry ↦ entry.1 ==
      (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] =
        [multicallCalldataPlan]) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.dynamicArray .bytes] cd =
      if solcSLT (solcSub cd.size 4) 32 then none
      else if solcMaxU64 < (calldataWord cd 4).toNat then none
      else if ArrayHeadChecks cd (arrayHead cd 4) then
        some ((∅ : Store).insert name (.array (calldataBytesArrayValues cd (arrayHead cd 4))))
      else none := by
  rw [decodeCalldataSolc08, if_neg (by omega : ¬ cd.size < 4)]
  simp only [decodeArgs?, List.isEmpty_cons, Bool.false_eq_true, if_false,
    show abiTupleHeadSize? [.dynamicArray .bytes] = some 32 from by
      simp only [abiTupleHeadSize?, isDynamicABIType, bind, Option.bind, if_true, Nat.add_zero],
    bind, Option.bind]
  by_cases hh : solcSLT (solcSub cd.size 4) 32 = true
  · simp only [hh, if_true]
  simp only [hh, hplans]
  simp only [decodeFields?, stride?, isDynamicABIType, if_true, List.headD_cons,
    retainFailure, show multicallCalldataPlan.deferErrors.contains [] = false from rfl,
    Bool.false_eq_true, if_false, solcTailTarget?, Bool.not_true,
    show solcAdd 4 0 = 4 from rfl, bind, Option.bind, Bool.and_false]
  have hr : solcReadNat cd.toList 4 = (calldataWord cd 4).toNat :=
    solcReadNat_word_total cd ⟨4⟩
  have hp : solcAdd 4 (calldataWord cd 4).toNat = (arrayHead cd 4).toNat := by
    exact solcAdd_word ⟨4⟩ (calldataWord cd 4)
  rw [hr]
  by_cases ho : solcMaxU64 < (calldataWord cd 4).toNat
  · simp only [ho, if_true]
  simp only [ho, if_false, hp]
  rw [decodeCalldataBytesArrayHead]
  by_cases hc : ArrayHeadChecks cd (arrayHead cd 4)
  · rw [if_pos hc, if_pos hc]
    rfl
  · rw [if_neg hc, if_neg hc]

-- LIBRARY CANDIDATE: the modern single-word head guard expressed by the reference decoder.
theorem solcCalldataHeadCheck {cd : ByteArray} (h4 : 4 ≤ cd.size)
    (hsize : cd.size < UInt256.size) :
    solcSLT (solcSub cd.size 4) 32 = false ↔ 36 ≤ cd.size ∧ cd.size < 2 ^ 255 + 4 := by
  have hs : solcSLT (solcSub cd.size 4) 32 = false ↔
      UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    by
      have h := solcSLT_word_false (UInt256.ofNat cd.size - ⟨4⟩) ⟨32⟩
      change solcSLT (solcSub cd.size 4) 32 = false ↔ _ at h
      exact h
  rw [hs]
  constructor
  · intro h
    constructor
    · by_contra hh
      rw [solcDecodeLenCheckShort_4_32 h4 (by omega) hsize] at h
      cases h
    · by_contra hh
      rw [solcDecodeLenCheckHuge_4_32 (by omega) hsize] at h
      cases h
  · rintro ⟨hlo, hhi⟩
    exact solcDecodeLenCheckOk_4_32 hlo hhi hsize

open Classical in
theorem decodeCalldataBytesArray {cd : ByteArray} (name : Ident)
    (table : List (Nat × List CalldataPlan)) (h4 : 4 ≤ cd.size)
    (hsize : cd.size < UInt256.size)
    (hplans : ((table.find? (fun entry ↦ entry.1 ==
      (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] =
        [multicallCalldataPlan]) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.dynamicArray .bytes] cd =
      if WordArrayCalldataChecks cd then
        some ((∅ : Store).insert name (.array (calldataBytesArrayValues cd (arrayHead cd 4))))
      else none := by
  rw [decodeCalldataBytesArrayRaw name table h4 hplans]
  by_cases hh : solcSLT (solcSub cd.size 4) 32 = false
  case neg =>
    have ht : solcSLT (solcSub cd.size 4) 32 = true := Bool.eq_true_of_not_eq_false hh
    rw [ht, if_pos rfl, if_neg (fun hc ↦ hh ((solcCalldataHeadCheck h4 hsize).mpr
      ⟨hc.head, by have := hc.size; omega⟩))]
  rw [hh]
  simp only [Bool.false_eq_true, if_false]
  have hb := (solcCalldataHeadCheck h4 hsize).mp hh
  by_cases ho : solcMaxU64 < (calldataWord cd 4).toNat
  · rw [if_pos ho, if_neg (fun hc ↦ (Nat.not_lt.mpr hc.offset) ho)]
  rw [if_neg ho]
  by_cases hc : ArrayHeadChecks cd (arrayHead cd 4)
  · rw [if_pos hc, if_pos (wordArrayCalldataChecks_of_runtime hb.1 hsize (by omega) hc)]
  · rw [if_neg hc, if_neg (fun h ↦ hc h.runtime)]

end Benchmarks.Morpho.MetaMorphoV1_1
