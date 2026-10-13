import Benchmarks.EAS.EAS.CalldataRead
import Benchmarks.EAS.EAS.SchemaABI
import Benchmarks.EAS.EAS.SchemaBuffer
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS

-- GENERALIZES decodeSolcBytes32 to padded reads and arbitrary decoder plans.
theorem decodeSolcBytes32_total (cd : ByteArray) (start : UInt256) (plan : CalldataPlan) (tailAccess : Bool) :
    decodeValue? abiBytes32 cd.toList start.toNat plan tailAccess =
      some (wordBytes32Value (calldataWord cd start.toNat)) := by
  rw [decodeValue?,solcReadBytes_word_total]
  have ht : (EVM.Word.toBytesBE (calldataWord cd start.toNat)).take 32 = EVM.Word.toBytesBE (calldataWord cd start.toNat) :=
    List.take_of_length_le (by rw [word_toBytesBE_length_32])
  rw [decodeABIValue_bytes32_ok (by rw [List.drop_zero,ht,word_toBytesBE_length_32])]
  simp only [Option.map_some,List.drop_zero,ht]

-- LIBRARY CANDIDATE: the modern unsigned decoder uses exactly the compiler's mask check.
theorem decodeUIntWord_mask (width : BitWidth) (w mask : UInt256)
    (hm : mask.toNat = 2^width.val-1) (hw : width.val ≠ 0) :
    decodeABIWord? (.elem (.int (.uint width))) w =
      if w = UInt256.land w mask then some (.int (Int.ofNat w.toNat)) else none := by
  have hc : w.toNat < EVM.twoPow width.val ↔ w = UInt256.land w mask := by
    constructor
    · intro h
      exact (u256LandMaskCleanOfToNat w mask hm h).symm
    · intro h
      simpa only [← h] using u256LandMaskToNatLtOfToNat w mask hm
  simp only [decodeABIWord?,hw,if_false]
  change (if w.toNat < EVM.twoPow width.val then _ else _) = _
  simp only [hc]
  rfl

-- LIBRARY CANDIDATE: strict Boolean decoding uses the double-ISZERO canonicality check.
theorem decodeBoolWord_clean (w : UInt256) :
    decodeABIWord? (.elem .bool) w =
      if w = UInt256.isZero (UInt256.isZero w) then some (.bool (decide (w.toNat ≠ 0))) else none := by
  rw [decodeBoolWord_eq]
  have he : (w.toNat = 0 ∨ w.toNat = 1) ↔ w = UInt256.isZero (UInt256.isZero w) := by
    rw [← boolWord_nat_iff,← boolWordClean_iff]
    exact eq_comm
  simp only [he]

end Benchmarks.EAS.EAS
