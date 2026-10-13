import Benchmarks.EAS.EAS.AttestationEncode
import Benchmarks.EAS.EAS.EncodeAttestationSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: the two usual formulas for ABI byte-string padding coincide.
theorem bytesPadding_eq_rounded (len : Nat) :
    bytesPadding len = 32*((len+31)/32)-len := by
  unfold bytesPadding
  omega

theorem AttestationRecord.encoding_size (a : AttestationRecord) :
    a.encoding.size = 352+32*((a.data.size+31)/32) := by
  simp only [AttestationRecord.encoding, ByteArray.size_append, wordBytes_size,
    AttestationRecord.words, List.length_append, List.length_cons, List.length_nil,
    ByteArray_zeroes_size, bytesPadding_eq_rounded]
  omega

theorem attestationRecordEncoded_read (mem : ByteArray) (src dst dataPtr : UInt256) (a : AttestationRecord)
    (hdlo : 96 ≤ dataPtr.toNat)
    (hdataDisj : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ dst.toNat)
    (hdataIn : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ mem.size)
    (hh : memLoad dataPtr mem = UInt256.ofNat a.data.size)
    (hhead : attestationEncodeHeadWords mem src = a.words ++ [UInt256.ofNat 320])
    (hdata : mem.readWithPadding (dataPtr.toNat+32) a.data.size = a.data)
    (hbound : dst.toNat+384+32*((a.data.size+31)/32) < UInt256.size) :
    (attestationEncodedMemory mem src dst dataPtr).readWithPadding dst.toNat a.encoding.size = a.encoding := by
  rw [a.encoding_size, attestationEncodedMemory_read mem src dst dataPtr a.data.size
    hdlo hdataDisj hdataIn hh hbound, hhead, hdata]
  simp only [AttestationRecord.encoding, wordBytes_append, wordBytes,
    ByteArray.append_empty, ByteArray.append_assoc, bytesPadding_eq_rounded]
  rfl

end Benchmarks.EAS.EAS
