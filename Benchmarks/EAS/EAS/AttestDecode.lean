import Benchmarks.EAS.EAS.ReferenceTail
import Benchmarks.EAS.EAS.WordArrayBase
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def attestRequestABI : ABIType := .tuple [abiBytes32,requestDataABI]
def attestRequestPlan : CalldataPlan := {materialize := [[.field 1]]}
def attestRequestData (cd : ByteArray) (root : UInt256) : UInt256 := root+calldataWord cd (root+UInt256.ofNat 32).toNat
def attestRequestValue (cd : ByteArray) (root : UInt256) : Value :=
  .tuple [wordBytes32Value (calldataWord cd root.toNat),(requestDataRecord cd (attestRequestData cd root)).tuple]
def attestRequestValid (cd : ByteArray) (root : UInt256) : Prop :=
  UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) root) ⟨64⟩ = ⟨0⟩ ∧
  requestReferenceValid cd root (root+UInt256.ofNat 32) ∧ requestDataValid cd (attestRequestData cd root)
instance (cd : ByteArray) (root : UInt256) : Decidable (attestRequestValid cd root) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem attestRequestFields_decode (cd : ByteArray) (root : UInt256) :
    (decodeFields? [abiBytes32,requestDataABI] cd.toList root.toNat 0 [{materialize := []},{}] false).map Value.tuple =
      if requestReferenceValid cd root (root+UInt256.ofNat 32) ∧ requestDataValid cd (attestRequestData cd root) then
        some (attestRequestValue cd root) else none := by
  have h0 : solcAdd root.toNat 0 = root.toNat := Nat.mod_eq_of_lt root.val.isLt
  have h32 : solcAdd root.toNat 32 = (root+UInt256.ofNat 32).toNat := solcAdd_word root (UInt256.ofNat 32)
  simp only [decodeFields?,show stride? abiBytes32 = some 32 from rfl,
    show stride? requestDataABI = some 32 by native_decide,
    show isDynamicABIType abiBytes32 = false from rfl,
    show isDynamicABIType requestDataABI = true by native_decide,
    List.headD_cons,List.tail_cons,retainFailure,List.contains_nil,if_false,if_true,
    Bool.false_eq_true,Bool.not_false,Bool.false_and,Bool.true_and,bind,Option.bind_some,
    Nat.zero_add,h0,h32,pure]
  rw [decodeSolcBytes32_total cd root {materialize := []} false,
    requestReference_decode cd root (root+UInt256.ofNat 32)]
  by_cases hr : requestReferenceValid cd root (root+UInt256.ofNat 32)
  · rw [if_pos hr]
    simp only [Option.bind_some]
    have hdata := requestData_decode cd (attestRequestData cd root) true
    change decodeValue? requestDataABI cd.toList (root+calldataWord cd (root+UInt256.ofNat 32).toNat).toNat {} true = _ at hdata
    rw [hdata]
    by_cases hd : requestDataValid cd (attestRequestData cd root)
    · rw [if_pos hd,if_pos ⟨hr,hd⟩]
      rfl
    · rw [if_neg hd,if_neg (fun h => hd h.2)]
      rfl
  · rw [if_neg hr,if_neg (fun h => hr h.1)]
    rfl

theorem attestRequest_decode (cd : ByteArray) (root : UInt256) :
    decodeValue? attestRequestABI cd.toList root.toNat attestRequestPlan false =
      if attestRequestValid cd root then some (attestRequestValue cd root) else none := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  have hs : solcSub cd.size root.toNat = (UInt256.sub (UInt256.ofNat cd.size) root).toNat := by
    unfold solcSub EVM.Word.ofNat
    rw [u256_ofNat_toNat]
    rfl
  rw [attestRequestABI,decodeValue?]
  simp only [show abiTupleHeadSize? [abiBytes32,requestDataABI] = some 64 by native_decide,
    show isDynamicABIType (.tuple [abiBytes32,requestDataABI]) = true by native_decide,
    show isMemory attestRequestPlan = false from rfl,
    show (List.range [abiBytes32,requestDataABI].length).map (fun i => child attestRequestPlan (.field i)) =
      [{materialize := []},{}] by native_decide,
    Bool.not_false,Bool.true_or,Bool.true_and,Bool.not_true,Bool.false_eq_true,if_false,
    bind,Option.bind_some,pure,hlen,hs]
  by_cases hh : UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) root) ⟨64⟩ = ⟨0⟩
  · have hc : solcSLT (UInt256.sub (UInt256.ofNat cd.size) root).toNat 64 = false :=
      (solcSLT_word_false _ (⟨64⟩ : UInt256)).mpr hh
    rw [hc]
    simp only [Bool.false_eq_true,if_false]
    have he := attestRequestFields_decode cd root
    simp only [attestRequestValid,hh,true_and]
    cases hd : decodeFields? [abiBytes32,requestDataABI] cd.toList root.toNat 0 [{materialize := []},{}] false <;>
      rw [hd] at he <;> exact he
  · have hc : solcSLT (UInt256.sub (UInt256.ofNat cd.size) root).toNat 64 = true := by
      cases hb : solcSLT (UInt256.sub (UInt256.ofNat cd.size) root).toNat 64
      · exact False.elim (hh ((solcSLT_word_false _ (⟨64⟩ : UInt256)).mp hb))
      · rfl
    rw [hc]
    simp only [if_true]
    rw [if_neg (fun h => hh h.1)]

def attestRoot (cd : ByteArray) : UInt256 := ⟨4⟩+calldataWord cd 4
def attestValid (cd : ByteArray) : Prop :=
  (calldataWord cd 4).toNat ≤ solcMaxU64 ∧ attestRequestValid cd (attestRoot cd)
instance (cd : ByteArray) : Decidable (attestValid cd) := inferInstanceAs (Decidable (_ ∧ _))

theorem decodeAttest {cd : ByteArray} (name : Ident) (table : List (Nat × List CalldataPlan))
    (h4 : 4 ≤ cd.size) (hhead : solcSLT (solcSub cd.size 4) 32 = false)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = [attestRequestPlan]) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [attestRequestABI] cd =
      if attestValid cd then some ((∅ : Store).insert name (attestRequestValue cd (attestRoot cd))) else none := by
  rw [decodeCalldataSolc08,if_neg (by omega : ¬ cd.size < 4)]
  simp only [decodeArgs?,List.isEmpty_cons,Bool.false_eq_true,if_false,
    show abiTupleHeadSize? [attestRequestABI] = some 32 by native_decide,
    bind,Option.bind_some,hhead,hplans]
  simp only [decodeFields?,show stride? attestRequestABI = some 32 by native_decide,
    show isDynamicABIType attestRequestABI = true by native_decide,
    if_true,if_false,List.headD_cons,List.tail_cons,retainFailure,
    show attestRequestPlan.deferErrors.contains [] = false from rfl,
    Bool.false_eq_true,solcTailTarget?,Bool.not_true,show solcAdd 4 0 = 4 from rfl,
    bind,Option.bind_some,Bool.true_and,Bool.and_false,pure]
  have hread : solcReadNat cd.toList 4 = (calldataWord cd 4).toNat := solcReadNat_word_total cd (⟨4⟩ : UInt256)
  rw [hread]
  by_cases ho : (calldataWord cd 4).toNat ≤ solcMaxU64
  · rw [if_neg (by omega : ¬ solcMaxU64 < (calldataWord cd 4).toNat)]
    have hp : solcAdd 4 (calldataWord cd 4).toNat = (attestRoot cd).toNat := solcAdd_word ⟨4⟩ (calldataWord cd 4)
    simp only [hp,Option.bind_some]
    rw [attestRequest_decode]
    by_cases hv : attestRequestValid cd (attestRoot cd)
    · rw [if_pos hv,if_pos ⟨ho,hv⟩]
      rfl
    · rw [if_neg hv,if_neg (fun h => hv h.2)]
      rfl
  · rw [if_pos (by omega : solcMaxU64 < (calldataWord cd 4).toNat),if_neg (fun h => ho h.1)]
    rfl

end Benchmarks.EAS.EAS
