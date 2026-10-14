import Benchmarks.Morpho.MetaMorphoV1_1.MulticallCalldataSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.CalldataReference

/-! Decoder equations for a calldata array whose byte strings are copied at each access. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

def calldataBytesArrayValues (cd : ByteArray) (head : UInt256) : List Value :=
  (List.range (calldataWord cd head.toNat).toNat).map
    (retainedCalldataElement .bytes multicallCalldataPlan cd.toList (head + ⟨32⟩).toNat 32)

-- LIBRARY CANDIDATE: top-level array decoding retains per-element failures.
theorem decodeRetainedArrayValue {ty : ABIType} {plan : CalldataPlan} {stride : Nat}
    (hs : stride? ty = some stride) (hn : (ty == .elem .bool) = false)
    (hf : (child plan .element).deferErrors.contains [] = true)
    (bytes : List UInt8) (start : Nat) :
    decodeValue? (.dynamicArray ty) bytes start plan false =
      if solcMaxU64 < solcReadNat bytes start ||
          badExtent (isMemory plan) false bytes start (solcReadNat bytes start) stride then
        none
      else some (.array ((List.range (solcReadNat bytes start)).map
        (retainedCalldataElement ty plan bytes (solcAdd start 32) stride))) := by
  have hc : (child plan .element).deferErrors.isEmpty = false := by
    cases h : (child plan .element).deferErrors with
    | nil => rw [h] at hf; cases hf
    | cons a rest => rfl
  rw [decodeValue?]
  simp only [hs, hc, Bool.and_false, Bool.false_eq_true, if_false, bind, Option.bind_some]
  split
  · rfl
  · have hd := decodeRetainedCalldataElements hs hn hf bytes (solcAdd start 32) 0
      (solcReadNat bytes start) true
    simp only [Nat.mul_zero, ← List.range_eq_range'] at hd
    rw [hd]
    rfl

theorem decodeCalldataBytesArrayValue (cd : ByteArray) (head : UInt256) :
    decodeValue? (.dynamicArray .bytes) cd.toList head.toNat multicallCalldataPlan false =
      if solcMaxU64 < (calldataWord cd head.toNat).toNat ||
          badExtent false false cd.toList head.toNat
            (calldataWord cd head.toNat).toNat 32 then none
      else some (.array (calldataBytesArrayValues cd head)) := by
  rw [decodeRetainedArrayValue rfl rfl (by decide), solcReadNat_word_total,
    show isMemory multicallCalldataPlan = false from rfl]
  have h32 : solcAdd head.toNat 32 = (head + ⟨32⟩).toNat := solcAdd_word head ⟨32⟩
  simp only [calldataBytesArrayValues, h32]

theorem calldataBytesArrayValues_length (cd : ByteArray) (head : UInt256) :
    (calldataBytesArrayValues cd head).length = (calldataWord cd head.toNat).toNat := by
  simp only [calldataBytesArrayValues, List.length_map, List.length_range]

theorem calldataBytesArrayValues_getElem (cd : ByteArray) (head : UInt256) (i : Nat)
    (hi : i < (calldataWord cd head.toNat).toNat) :
    (calldataBytesArrayValues cd head)[i]? =
      some (retainedCalldataElement .bytes multicallCalldataPlan cd.toList
        (head + ⟨32⟩).toNat 32 i) := by
  rw [List.getElem?_eq_getElem (by rwa [calldataBytesArrayValues_length])]
  simp only [calldataBytesArrayValues, List.getElem_map, List.getElem_range]

end Benchmarks.Morpho.MetaMorphoV1_1
