import Benchmarks.EAS.EAS.Signature
import Benchmarks.EAS.EAS.RevokeDecode
import Benchmarks.EAS.EAS.CalldataScalar
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def abiUInt8 : ABIType := .elem (.int (.uint ⟨8,by decide⟩))
def signatureABI : ABIType := .tuple [abiUInt8,abiBytes32,abiBytes32]
def signatureRecord (cd : ByteArray) (start : Nat) : SignatureRecord :=
  ⟨calldataWord cd start,calldataWord cd (start+32),calldataWord cd (start+64)⟩
def signatureClean (s : SignatureRecord) : Prop := s.v = UInt256.land s.v (UInt256.ofNat 255)
instance (s : SignatureRecord) : Decidable (signatureClean s) := inferInstanceAs (Decidable (_ = _))

theorem decodeSignatureTuple {bytes : List UInt8} {start : Nat}
    (ha : ((bytes.drop start).take 32).length = 32)
    (hb : ((bytes.drop (start+32)).take 32).length = 32)
    (hc : ((bytes.drop (start+64)).take 32).length = 32) :
    decodeABIValue? signatureABI bytes start =
      (decodeABIWord? abiUInt8 (bytesToWord ((bytes.drop start).take 32))).map
        (fun val => (.tuple [val,.fixedBytes abiBytes32Width ((bytes.drop (start+32)).take 32),
          .fixedBytes abiBytes32Width ((bytes.drop (start+64)).take 32)],start+96)) := by
  rw [signatureABI,decodeABIValue?]
  simp only [bind,show abiTupleHeadSize? [abiUInt8,abiBytes32,abiBytes32] = some 96 by native_decide,Option.bind]
  simp only [decodeABIValues?,show isDynamicABIType abiUInt8 = false from rfl,
    show isDynamicABIType abiBytes32 = false from rfl,
    show staticABIEncodedSize? abiUInt8 = some 32 from rfl,
    show staticABIEncodedSize? abiBytes32 = some 32 from rfl,
    Bool.false_eq_true,if_false,bind,Option.bind,Nat.add_zero,Nat.zero_add]
  rw [decodeABIValue_scalarWord_eq (ty := abiUInt8) (by rfl)]
  simp only [decodeScalarWord?,readWord?,readBytes?,ha,if_true,bind,Option.bind,pure]
  rw [decodeABIValue_bytes32_ok hb,decodeABIValue_bytes32_ok (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hc)]
  cases decodeABIWord? abiUInt8 (bytesToWord ((bytes.drop start).take 32)) <;>
    simp only [Option.bind_some,Option.bind_none,bind,if_true,Option.map_some,Option.map_none,pure,Nat.add_assoc,Nat.reduceAdd,
      Nat.max_eq_left (by omega : start+64 ≤ start+96),Nat.max_eq_left (by omega : start+32 ≤ start+96),Nat.max_self]

end Benchmarks.EAS.EAS
