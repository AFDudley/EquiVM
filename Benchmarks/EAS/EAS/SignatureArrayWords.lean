import Benchmarks.EAS.EAS.CheckedArrayDecode
import Benchmarks.EAS.EAS.RevocationArrayWords
import Benchmarks.EAS.EAS.SignatureCalldata
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def signatureRecords (cd : ByteArray) (start n : Nat) : List SignatureRecord :=
  (List.range n).map (fun i => signatureRecord cd (start+96*i))
theorem signatureRecords_length (cd : ByteArray) (start n : Nat) : (signatureRecords cd start n).length = n := by
  simp only [signatureRecords,List.length_map,List.length_range]
theorem signatureRecords_get (cd : ByteArray) (start n i : Nat) (hi : i<(signatureRecords cd start n).length) :
    (signatureRecords cd start n)[i] = signatureRecord cd (start+96*i) := by
  simp only [signatureRecords,List.getElem_map,List.getElem_range]

theorem signatureArrayWords_decode {cd : ByteArray} {start n : Nat}
    (hb : start+96*n ≤ cd.size) (hsize : cd.size < UInt256.size) :
    decodeABIArrayStaticElems? signatureABI n 96 (solcReadWords cd.toList start (3*n)) 0 =
      if ∀ s∈signatureRecords cd start n,signatureClean s then
        some ((signatureRecords cd start n).map SignatureRecord.tuple,96*n) else none := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  rw [solcReadWords_slice (by rw [hlen]; omega) (by rw [hlen]; exact hsize),show 32*(3*n) = 96*n by omega]
  let ss := signatureRecords cd start n
  have hdec := decodeStaticArray_of_checked_elements SignatureRecord.tuple signatureClean
    (ty := signatureABI) (start := 0) (stride := 96) (xs := ss)
    (bytes := (cd.toList.drop start).take (96*n)) (by
      intro i hi
      have hin : i<n := by simpa only [ss,signatureRecords_length] using hi
      have hv := calldataSlice_word (off := 96*i) hb (by omega)
      have hr := calldataSlice_word (off := 96*i+32) hb (by omega)
      have hs := calldataSlice_word (off := 96*i+64) hb (by omega)
      have ht := decodeSignatureTuple (start := 96*i)
        (by rw [hv,word_toBytesBE_length_32]) (by rw [hr,word_toBytesBE_length_32]) (by rw [hs,word_toBytesBE_length_32])
      rw [hv,hr,hs,bytesToWord_toBytesBE] at ht
      rw [show abiUInt8 = .elem (.int (.uint ⟨8,by decide⟩)) from rfl,
        decodeUIntWord_mask ⟨8,by decide⟩ _ (UInt256.ofNat 255) rfl (by decide)] at ht
      simp only [Nat.zero_add,ss,signatureRecords_get]
      by_cases hc : signatureClean (signatureRecord cd (start+96*i))
      · rw [if_pos hc]
        have hvclean : calldataWord cd (start+96*i) = UInt256.land (calldataWord cd (start+96*i)) (UInt256.ofNat 255) := hc
        rw [if_pos hvclean,Option.map_some] at ht
        convert ht using 1 <;> simp only [signatureRecord,SignatureRecord.tuple,wordBytes32Value,Nat.add_assoc,Nat.mul_add,Nat.mul_one]
      · rw [if_neg hc]
        have hvdirty : ¬ calldataWord cd (start+96*i) = UInt256.land (calldataWord cd (start+96*i)) (UInt256.ofNat 255) := hc
        rw [if_neg hvdirty,Option.map_none] at ht
        exact ht)
  simpa only [ss,signatureRecords_length,Nat.zero_add] using hdec

end Benchmarks.EAS.EAS
