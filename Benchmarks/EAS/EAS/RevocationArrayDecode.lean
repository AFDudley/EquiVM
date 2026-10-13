import Benchmarks.EAS.EAS.RevocationArrayWords
import Benchmarks.EAS.EAS.CalldataArrayExtent
import Benchmarks.EAS.EAS.CalldataGuards
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def revocationArrayHeaderValid (cd : ByteArray) (header : UInt256) : Prop :=
  (calldataWord cd header.toNat).toNat ≤ 2^64-1 ∧
  UInt256.gt ((header+UInt256.ofNat 32)+UInt256.shiftLeft (calldataWord cd header.toNat) (UInt256.ofNat 6))
    (UInt256.ofNat cd.size) = ⟨0⟩
instance (cd : ByteArray) (header : UInt256) : Decidable (revocationArrayHeaderValid cd header) :=
  inferInstanceAs (Decidable (_ ∧ _))

def decodeRevocationArray (cd : ByteArray) (header : UInt256) : Option (List RevocationRequestRecord) :=
  if revocationArrayHeaderValid cd header then
    some (revocationRecords cd (header+UInt256.ofNat 32).toNat (calldataWord cd header.toNat).toNat) else none

theorem revocationArrayHeaderValid.extent {cd : ByteArray} {header : UInt256}
    (h : revocationArrayHeaderValid cd header) (hsize : cd.size < 2^255+4) :
    (header+UInt256.ofNat 32).toNat+64*(calldataWord cd header.toNat).toNat ≤ cd.size := by
  have hn := h.1
  apply calldataArrayExtent_stride hsize (by omega)
  simpa only [wordShiftLeft_nat _ 6 (by decide),show 2^6 = 64 from rfl] using h.2

theorem revocationArray_decode (cd : ByteArray) (header : UInt256) (hsize : cd.size < 2^255+4) :
    decodeValue? (.dynamicArray revocationDataABI) cd.toList header.toNat {} true =
      (decodeRevocationArray cd header).map (fun rs => Value.array (rs.map RevocationRequestRecord.tuple)) := by
  let len := calldataWord cd header.toNat
  let offset := header+UInt256.ofNat 32
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  have h32 : solcAdd header.toNat 32 = offset.toNat := solcAdd_word header (UInt256.ofNat 32)
  rw [decodeValue?,solcReadNat_word_total]
  simp only [show stride? revocationDataABI = some 64 by native_decide,
    show isDynamicABIType revocationDataABI = false from rfl,
    show isMemory ({} : CalldataPlan) = true from rfl,
    show (child ({} : CalldataPlan) .element).deferErrors.isEmpty = true from rfl,
    Bool.not_false,Bool.true_and,if_true,bind,Option.bind_some]
  by_cases hl : len.toNat ≤ 2^64-1
  · have hl' : ¬ solcMaxU64 < (calldataWord cd header.toNat).toNat := by change ¬ 18446744073709551615 < len.toNat; omega
    simp only [hl',decide_false,Bool.false_or,badExtent,Bool.not_true,Bool.false_and,Bool.true_and,Bool.false_eq_true,if_false,hlen,h32]
    have hshift : UInt256.shiftLeft len (UInt256.ofNat 6) = UInt256.ofNat (64*len.toNat) := wordShiftLeft_nat len 6 (by decide)
    have hs : solcAdd offset.toNat ((calldataWord cd header.toNat).toNat*64) =
        (offset+UInt256.shiftLeft len (UInt256.ofNat 6)).toNat := by
      rw [hshift]
      have hn : (UInt256.ofNat (64*len.toNat)).toNat = 64*len.toNat := ulit_toNat' _ (by change _ < 2^256; omega)
      have he := solcAdd_word offset (UInt256.ofNat (64*len.toNat))
      rw [hn] at he
      simpa only [Nat.mul_comm,len] using he
    rw [hs]
    have hmod : cd.size % EVM.wordModulus = (UInt256.ofNat cd.size).toNat := rfl
    rw [hmod]
    by_cases he : UInt256.gt (offset+UInt256.shiftLeft len (UInt256.ofNat 6)) (UInt256.ofNat cd.size) = ⟨0⟩
    · have he' := ugt_eq_zero_to_le he
      simp only [show ¬ (UInt256.ofNat cd.size).toNat < (offset+UInt256.shiftLeft len (UInt256.ofNat 6)).toNat by omega,
        decide_false,if_false]
      have hh : revocationArrayHeaderValid cd header := ⟨hl,he⟩
      have hc := hh.extent hsize
      rw [show (calldataWord cd header.toNat).toNat*64/32 = 2*(calldataWord cd header.toNat).toNat by omega,
        revocationArrayWords_decode hc (by change cd.size < 2^256; omega),decodeRevocationArray,if_pos hh]
      rfl
    · have he' : (UInt256.ofNat cd.size).toNat < (offset+UInt256.shiftLeft len (UInt256.ofNat 6)).toNat := by
        have h := (word_gt_zero _ _).not.mp he
        omega
      simp only [he',decide_true,if_true]
      rw [decodeRevocationArray,if_neg (fun (h : revocationArrayHeaderValid cd header) => he h.2)]
      rfl
  · have hl' : solcMaxU64 < (calldataWord cd header.toNat).toNat := by change 18446744073709551615 < len.toNat; omega
    simp only [hl',decide_true,Bool.true_or,if_true]
    rw [decodeRevocationArray,if_neg (fun h => hl h.1)]
    rfl


structure RevocationArrayCalldataView (cd : ByteArray) (offset : UInt256) (rs : List RevocationRequestRecord) : Prop where
  extent : offset.toNat+64*rs.length ≤ cd.size
  requests : ∀ i (hi : i < rs.length), revocationDataRecord cd (offset.toNat+64*i) = rs[i]

theorem decodeRevocationArray_facts {cd : ByteArray} {header : UInt256} {rs : List RevocationRequestRecord}
    (hsize : cd.size < 2^255+4) (h : decodeRevocationArray cd header = some rs) :
    revocationArrayHeaderValid cd header ∧ rs.length = (calldataWord cd header.toNat).toNat ∧
    RevocationArrayCalldataView cd (header+UInt256.ofNat 32) rs := by
  unfold decodeRevocationArray at h
  split at h
  · obtain ⟨rfl⟩ := Option.some.inj h
    exact ⟨‹revocationArrayHeaderValid cd header›,revocationRecords_length _ _ _,
      by simpa only [revocationRecords_length] using (‹revocationArrayHeaderValid cd header›).extent hsize,
      fun i hi => (revocationRecords_get _ _ _ i hi).symm⟩
  · contradiction

end Benchmarks.EAS.EAS
