import Benchmarks.EAS.EAS.CalldataBytes
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a padded calldata read always has the requested length.
theorem calldataRead_size (cd : ByteArray) (start size : Nat) :
    (cd.readBytes start size).size = size := by
  have he := congrArg List.length (readBytes_padded_toList cd start size)
  rw [byteArray_toList_eq,Array.length_toList] at he
  simp only [List.length_append,List.length_replicate,List.length_take,List.length_drop] at he
  change _ = size
  change (cd.readBytes start size).size = _ at he
  omega

-- LIBRARY CANDIDATE: a calldata word whose starting address is beyond the input is zero.
theorem calldataWord_zero_of_ge (cd : ByteArray) (start : Nat) (h : cd.size ≤ start) :
    calldataWord cd start = ⟨0⟩ := by
  have hd : cd.toList.drop start = [] := List.drop_eq_nil_iff.mpr (by
    rw [byteArray_toList_eq,Array.length_toList]
    exact h)
  have hb : cd.readBytes start 32 = (⟨0⟩ : UInt256).toByteArray := by
    apply byteArray_eq_of_toList_eq
    rw [readBytes_padded_toList,hd]
    simp only [List.take_nil,List.length_nil,Nat.sub_zero,List.nil_append]
    native_decide
  change uInt256OfByteArray _ = _
  rw [hb,uInt256OfByteArray_toByteArray]

-- LIBRARY CANDIDATE: bounded byte lengths make every nonempty accepted calldata payload complete.
theorem calldataPayload_complete {cd : ByteArray} {start : UInt256}
    (hsize : cd.size < 2^255+4)
    (hlen : (calldataWord cd start.toNat).toNat ≤ 2^64-1)
    (hend : UInt256.gt ((start+calldataWord cd start.toNat)+⟨32⟩) (UInt256.ofNat cd.size) = ⟨0⟩) :
    (calldataWord cd start.toNat).toNat = 0 ∨
      start.toNat+32+(calldataWord cd start.toNat).toNat ≤ cd.size := by
  by_cases hz : (calldataWord cd start.toNat).toNat = 0
  · exact Or.inl hz
  · right
    have hs : start.toNat < cd.size := by
      by_contra hn
      have he := calldataWord_zero_of_ge cd start.toNat (by omega)
      exact hz (congrArg UInt256.toNat he)
    have hp : start.toNat+(calldataWord cd start.toNat).toNat < UInt256.size := by
      change _ < 2^256
      omega
    have hn : (start+calldataWord cd start.toNat).toNat = start.toNat+(calldataWord cd start.toNat).toNat :=
      by rw [uadd_toNat,Nat.mod_eq_of_lt hp]
    have he := ugt_eq_zero_to_le hend
    change ((start+calldataWord cd start.toNat)+UInt256.ofNat 32).toNat ≤ (UInt256.ofNat cd.size).toNat at he
    rw [uadd_word_ofNat_toNat (start+calldataWord cd start.toNat) 32 (by rw [hn]; change _ < 2^256; omega),
      hn,ulit_toNat' cd.size (by change cd.size < 2^256; omega)] at he
    omega

end Benchmarks.EAS.EAS
