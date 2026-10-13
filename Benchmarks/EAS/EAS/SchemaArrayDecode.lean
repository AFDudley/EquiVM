import Benchmarks.EAS.EAS.ReferenceTail
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiRequestPlan : CalldataPlan := {materialize := [[.element,.field 1]],deferErrors := [[.element]]}
def multiRequestRowPlan : CalldataPlan := {materialize := [[.field 1]],deferErrors := [[]]}
def multiRequestRoot (cd : ByteArray) (base : UInt256) (i : Nat) : UInt256 :=
  base+calldataWord cd (base.toNat+32*i)
def multiRequestArray (cd : ByteArray) (root : UInt256) : UInt256 :=
  root+calldataWord cd (root+UInt256.ofNat 32).toNat

def multiRequestReferenceValid (cd : ByteArray) (base : UInt256) (i : Nat) : Prop :=
  UInt256.isZero (UInt256.slt (calldataWord cd (base.toNat+32*i))
    ((UInt256.ofNat cd.size-base)-⟨63⟩)) = ⟨0⟩
instance (cd : ByteArray) (base : UInt256) (i : Nat) : Decidable (multiRequestReferenceValid cd base i) :=
  inferInstanceAs (Decidable (_ = _))
def requestArrayReferenceValid (cd : ByteArray) (root : UInt256) : Prop :=
  UInt256.isZero (UInt256.slt (calldataWord cd (root+UInt256.ofNat 32).toNat)
    ((UInt256.ofNat cd.size-root)-⟨31⟩)) = ⟨0⟩
instance (cd : ByteArray) (root : UInt256) : Decidable (requestArrayReferenceValid cd root) :=
  inferInstanceAs (Decidable (_ = _))

-- LIBRARY CANDIDATE: decode the fields of a referenced bytes32/array tuple.
theorem schemaArrayFields_decode (ty : ABIType) (cd : ByteArray) (root : UInt256)
    (decode : UInt256 → Option Value)
    (hdecode : ∀ header, decodeValue? (.dynamicArray ty) cd.toList header.toNat {} true = decode header) :
    (decodeFields? [abiBytes32,.dynamicArray ty] cd.toList root.toNat 0
      [{materialize := []},{}] false).map Value.tuple =
      (if requestArrayReferenceValid cd root then decode (multiRequestArray cd root) else none).map
        (fun value => Value.tuple [wordBytes32Value (calldataWord cd root.toNat),value]) := by
  have h0 : solcAdd root.toNat 0 = root.toNat := Nat.mod_eq_of_lt root.val.isLt
  have h32 : solcAdd root.toNat 32 = (root+UInt256.ofNat 32).toNat := solcAdd_word root (UInt256.ofNat 32)
  have href : solcTailTarget? true (.dynamicArray ty) cd.toList root.toNat (root+UInt256.ofNat 32).toNat =
      if requestArrayReferenceValid cd root then some (multiRequestArray cd root).toNat else none := by
    simpa only [requestArrayReferenceValid,multiRequestArray,
      show (⟨32⟩ : UInt256)-⟨1⟩ = (⟨31⟩ : UInt256) from rfl] using
      solcTailTarget_reference cd root (root+UInt256.ofNat 32) ⟨32⟩ (.dynamicArray ty) rfl
  simp only [decodeFields?,show stride? abiBytes32 = some 32 from rfl,
    show stride? (.dynamicArray ty) = some 32 from rfl,
    show isDynamicABIType abiBytes32 = false from rfl,
    show isDynamicABIType (.dynamicArray ty) = true from rfl,
    List.headD_cons,List.tail_cons,retainFailure,List.contains_nil,if_false,if_true,
    Bool.false_eq_true,Bool.not_false,Bool.false_and,Bool.true_and,bind,Option.bind_some,
    Nat.zero_add,h0,h32,pure]
  rw [decodeSolcBytes32_total cd root {materialize := []} false,href]
  by_cases hr : requestArrayReferenceValid cd root
  · simp only [if_pos hr]
    simp only [Option.bind_some]
    rw [hdecode]
    cases decode (multiRequestArray cd root) <;> rfl
  · simp only [if_neg hr]
    rfl

-- LIBRARY CANDIDATE: a tuple retained in calldata exposes the field decoder directly.
theorem schemaArray_decode (ty : ABIType) (cd : ByteArray) (root : UInt256) :
    decodeValue? (.tuple [abiBytes32,.dynamicArray ty]) cd.toList root.toNat multiRequestRowPlan true =
      (decodeFields? [abiBytes32,.dynamicArray ty] cd.toList root.toNat 0
        [{materialize := []},{}] false).map Value.tuple := by
  rw [decodeValue?]
  simp only [show abiTupleHeadSize? [abiBytes32,.dynamicArray ty] = some 64 by
      simp only [abiTupleHeadSize?,abiBytes32,isDynamicABIType,staticABIEncodedSize?,Bool.false_eq_true,if_true,if_false,bind,Option.bind],
    show isDynamicABIType (.tuple [abiBytes32,.dynamicArray ty]) = true from rfl,
    show isMemory multiRequestRowPlan = false from rfl,
    show (List.range [abiBytes32,.dynamicArray ty].length).map (fun i => child multiRequestRowPlan (.field i)) =
      [{materialize := []},{}] by
      change (List.range 2).map (fun i => child multiRequestRowPlan (.field i)) = _
      native_decide,
    Bool.not_true,Bool.false_or,Bool.false_and,Bool.false_eq_true,if_false,
    bind,Option.bind_some,pure]
  cases decodeFields? [abiBytes32,.dynamicArray ty] cd.toList root.toNat 0
    [{materialize := []},{}] false <;> rfl

-- LIBRARY CANDIDATE: the outer offset of a schema/array tuple uses a 64-byte reference check.
theorem schemaArrayElement_decode (ty : ABIType) (cd : ByteArray) (base : UInt256) (i : Nat)
    (hb : base.toNat+32*i < UInt256.size) :
    (do
      let target ← solcTailTarget? true (.tuple [abiBytes32,.dynamicArray ty]) cd.toList base.toNat (solcAdd base.toNat (32*i))
      decodeValue? (.tuple [abiBytes32,.dynamicArray ty]) cd.toList target multiRequestRowPlan true) =
      if multiRequestReferenceValid cd base i then
        decodeValue? (.tuple [abiBytes32,.dynamicArray ty]) cd.toList (multiRequestRoot cd base i).toNat multiRequestRowPlan true
      else none := by
  have hslot : solcAdd base.toNat (32*i) = (UInt256.ofNat (base.toNat+32*i)).toNat := by
    rw [ulit_toNat' _ hb]; exact Nat.mod_eq_of_lt hb
  have href := solcTailTarget_reference cd base (UInt256.ofNat (base.toNat+32*i)) ⟨64⟩
    (.tuple [abiBytes32,.dynamicArray ty]) (by
      simp only [tailSize?,abiTupleHeadSize?,abiBytes32,isDynamicABIType,staticABIEncodedSize?,if_true,if_false,bind,Option.bind]
      rfl)
  rw [ulit_toNat' _ hb] at href
  change solcTailTarget? true (.tuple [abiBytes32,.dynamicArray ty]) cd.toList base.toNat (base.toNat+32*i) =
    if multiRequestReferenceValid cd base i then some (multiRequestRoot cd base i).toNat else none at href
  simp only [hslot,ulit_toNat' _ hb,href,bind]
  by_cases hr : multiRequestReferenceValid cd base i
  · simp only [if_pos hr,Option.bind_some]
  · simp only [if_neg hr]
    rfl

end Benchmarks.EAS.EAS
