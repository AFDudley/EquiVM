import Benchmarks.EAS.EAS.RecordMemory
import Benchmarks.EAS.EAS.ResolverOneSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolverOneSelectorWord (rev : Bool) : UInt256 :=
  if rev then UInt256.ofNat 0xe49617e100000000000000000000000000000000000000000000000000000000
  else UInt256.ofNat 0xe60c350500000000000000000000000000000000000000000000000000000000

theorem resolverOneSelectorWord_bytes (rev : Bool) :
    (resolverOneSelectorWord rev).toByteArray.extract 0 4 = (resolverOneSelector rev).toByteArray := by
  cases rev <;> decide +kernel

theorem resolverOnePayload_size (a : AttestationRecord) (rev : Bool) :
    (resolverOnePayload a rev).size = 36+a.encoding.size := by
  have hlen : (resolverOneSelector rev).length = 4 := by cases rev <;> rfl
  simp only [resolverOnePayload, ByteArray.size_append, list_toByteArray_size, toByteArray_size, hlen]
  omega

def resolverOneHeaderMemory (mem : ByteArray) (ptr : UInt256) (rev : Bool) : ByteArray :=
  selectorArgumentMemory mem ptr.toNat (resolverOneSelectorWord rev) (UInt256.ofNat 32)

def resolverOneEncodedMemory (mem : ByteArray) (src ptr dataPtr : UInt256) (rev : Bool) : ByteArray :=
  attestationEncodedMemory (resolverOneHeaderMemory mem ptr rev) src (ptr+UInt256.ofNat 36) dataPtr

theorem resolverOneHeaderMemory_eq (mem : ByteArray) (ptr : UInt256) (rev : Bool)
    (hh : memLoad (UInt256.ofNat 64) mem = ptr) (hb : ptr.toNat+36 < UInt256.size) :
    (if rev then easBlocks.eas_block_15794_memory (mem := mem) (x2 := UInt256.ofNat 32)
      else easBlocks.eas_block_16004_memory (mem := mem) (x2 := UInt256.ofNat 32)) =
      resolverOneHeaderMemory mem ptr rev := by
  have h4 : (ptr+UInt256.ofNat 4).toNat = ptr.toNat+4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  cases rev <;> simp only [Bool.false_eq_true, if_false, if_true, easBlocks.eas_block_15794_memory,
    easBlocks.eas_block_16004_memory, hh, h4, resolverOneHeaderMemory, selectorArgumentMemory,
    resolverOneSelectorWord, writeWord_as_write]

theorem resolverOneHeaderMemory_view {mem : ByteArray} {src ptr dataPtr : UInt256} {rev : Bool} {a : AttestationRecord}
    (hv : AttestationMemoryView mem src dataPtr a)
    (hs : src.toNat+320 ≤ ptr.toNat) (hd : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ ptr.toNat) :
    AttestationMemoryView (resolverOneHeaderMemory mem ptr rev) src dataPtr a :=
  hv.preserve (selectorArgumentMemory_prefix mem ptr.toNat _ _) hs hd ptr.val.isLt

theorem resolverOneEncodedMemory_read {mem : ByteArray} {src ptr dataPtr : UInt256} {rev : Bool} {a : AttestationRecord}
    (hv : AttestationMemoryView mem src dataPtr a)
    (hs : src.toNat+320 ≤ ptr.toNat) (hd : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ ptr.toNat)
    (hb : ptr.toNat+420+32*((a.data.size+31)/32) < UInt256.size) :
    (resolverOneEncodedMemory mem src ptr dataPtr rev).readWithPadding ptr.toNat (resolverOnePayload a rev).size =
      resolverOnePayload a rev := by
  let head := resolverOneHeaderMemory mem ptr rev
  let dst := ptr+UInt256.ofNat 36
  have hdst : dst.toNat = ptr.toNat+36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have hv' : AttestationMemoryView head src dataPtr a := resolverOneHeaderMemory_view hv hs hd
  have hbound : dst.toNat+384+32*((a.data.size+31)/32) < UInt256.size := by rw [hdst]; omega
  have hdisj : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ dst.toNat := by rw [hdst]; omega
  have hout := attestationRecordEncoded_read head src dst dataPtr a hv'.dataLow hdisj hv'.dataCovered
    hv'.length hv'.fields hv'.payload hbound
  have hp := attestationEncodedMemory_prefix head src dst dataPtr a.data.size hv'.dataLow hdisj hv'.dataCovered hv'.length hbound
  have hc := attestationEncodedMemory_covers head src dst dataPtr a.data.size hv'.dataLow hdisj hv'.dataCovered hv'.length hbound
  have hheader : (attestationEncodedMemory head src dst dataPtr).readWithPadding ptr.toNat 36 =
      (resolverOneSelector rev).toByteArray ++ (UInt256.ofNat 32).toByteArray := by
    rw [← resolverOneSelectorWord_bytes rev]
    exact selectorArgumentMemory_read_of_prefix hp (by have h := hv.sourceLow; omega) (by rw [hdst]) (by omega)
  change (attestationEncodedMemory head src dst dataPtr).readWithPadding ptr.toNat (resolverOnePayload a rev).size = _
  rw [resolverOnePayload_size, byteArray_readWithPadding_split_unbounded _ _ 36 a.encoding.size
    (by decide) (by rw [a.encoding_size]; omega) (by rw [hdst] at hc; rw [a.encoding_size]; omega),
    hheader, ← hdst, hout]
  exact ByteArray.append_assoc

end Benchmarks.EAS.EAS
