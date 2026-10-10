import Benchmarks.EAS.EAS.CalldataPayload
import Benchmarks.EAS.EAS.CopyEncodeViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a zero-length calldata read is empty at every address.
theorem calldataRead_zero (cd : ByteArray) (start : Nat) : cd.readBytes start 0 = ByteArray.empty := by
  apply byteArray_eq_of_toList_eq
  rw [readBytes_padded_toList]
  simp only [List.take_zero,List.length_nil,Nat.sub_self,List.replicate_zero,List.append_nil]
  rw [byteArray_toList_eq]
  rfl

-- GENERALIZES readBytes_at_toList_any from one word to any complete slice.
theorem calldataRead_extract (cd : ByteArray) (start size : Nat) (hb : start+size ≤ cd.size) :
    cd.readBytes start size = cd.extract start (start+size) := by
  have hlen : ((cd.toList.drop start).take size).length = size := by
    rw [List.length_take,List.length_drop,byteArray_toList_eq,Array.length_toList]
    change min size (cd.size-start) = size
    omega
  apply byteArray_eq_of_toList_eq
  rw [readBytes_padded_toList,hlen]
  simp only [Nat.sub_self,List.replicate_zero,List.append_nil,extract_toList,Nat.add_sub_cancel_left]

-- LIBRARY CANDIDATE: accepted calldata payloads also have a complete wrapping-address copy.
theorem calldataPayload_bounds {cd : ByteArray} {start : UInt256}
    (hsize : cd.size < 2^255+4)
    (hlen : (calldataWord cd start.toNat).toNat ≤ 2^64-1)
    (hend : UInt256.gt ((start+calldataWord cd start.toNat)+⟨32⟩) (UInt256.ofNat cd.size) = ⟨0⟩) :
    ((calldataWord cd start.toNat).toNat=0 ∨
      (start+⟨32⟩).toNat+(calldataWord cd start.toNat).toNat ≤ cd.size) ∧
    cd.readBytes (start+⟨32⟩).toNat (calldataWord cd start.toNat).toNat =
      cd.readBytes (start.toNat+32) (calldataWord cd start.toNat).toNat := by
  rcases calldataPayload_complete hsize hlen hend with hz|hc
  · rw [hz,calldataRead_zero,calldataRead_zero]
    exact ⟨Or.inl rfl,rfl⟩
  · have hn : (start+⟨32⟩).toNat = start.toNat+32 :=
      uadd_word_ofNat_toNat start 32 (by change _ < 2^256; omega)
    rw [hn]
    exact ⟨Or.inr hc,rfl⟩

-- LIBRARY CANDIDATE: a complete (or empty) calldata copy preserves disjoint words.
theorem calldataCopy_read (cd mem : ByteArray) (src dst len read : Nat)
    (hsrc : len = 0 ∨ src+len ≤ cd.size) (hdst : dst ≤ mem.size)
    (hin : read+32 ≤ mem.size) (hdisj : read+32 ≤ dst ∨ dst+len ≤ read) :
    (cd.write src mem dst len).readWithPadding read 32 = mem.readWithPadding read 32 := by
  by_cases hz : len=0
  · rw [hz,byteArray_write_len_zero]
  · exact copyWindow_read_preserved cd mem src dst len read hz (hsrc.resolve_left hz) hdst hin hdisj

theorem calldataCopy_prefix (cd mem : ByteArray) (src dst len limit : Nat)
    (hsrc : len=0 ∨ src+len ≤ cd.size) (hdst : dst ≤ mem.size) (hl : limit ≤ dst) :
    MemoryPrefix mem (cd.write src mem dst len) limit :=
  ⟨byteArray_write_size_ge_base _ _ _ _ _,fun read _ hhi hin =>
    calldataCopy_read cd mem src dst len read hsrc hdst hin (Or.inl (le_trans hhi hl))⟩

-- LIBRARY CANDIDATE: a complete calldata copy reads back as the corresponding padded slice.
theorem calldataCopy_payload (cd mem : ByteArray) (src dst len : Nat)
    (hsrc : len=0 ∨ src+len ≤ cd.size) (hdst : dst ≤ mem.size) :
    dst+len ≤ (cd.write src mem dst len).size ∧
    (cd.write src mem dst len).readWithPadding dst len = cd.readBytes src len := by
  by_cases hz : len=0
  · subst len
    simp only [byteArray_write_len_zero,Nat.add_zero,byteArray_readWithPadding_zero,calldataRead_zero,and_true]
    exact hdst
  · have hs := hsrc.resolve_left hz
    have hc : dst+len ≤ (cd.write src mem dst len).size := by
      rw [copyWindow_size _ _ _ _ _ hz hs hdst]
      omega
    refine ⟨hc,?_⟩
    rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) hc,calldataRead_extract cd src len hs]
    simpa only [Nat.add_zero] using copyWindow_extract cd mem src dst len 0 len hz hs hdst (by omega)

end Benchmarks.EAS.EAS
