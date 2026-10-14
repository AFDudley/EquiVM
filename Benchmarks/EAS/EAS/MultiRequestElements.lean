import Benchmarks.EAS.EAS.MultiRequestDecode
import Benchmarks.EAS.EAS.ReferencedArrayDecode
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiRequestValues (cd : ByteArray) (base : UInt256) (n : Nat) : List Value :=
  (List.range n).map (multiRequestValue cd base)

theorem multiRequestElements_decode (cd : ByteArray) (base : UInt256) (i n : Nat)
    (hb : base.toNat+32*(i+n) < UInt256.size) (hsize : cd.size < 2^255+4) :
    decodeElements? multiRequestABI n cd.toList base.toNat (32*i) multiRequestPlan true =
      some ((List.range' i n).map (multiRequestValue cd base)) := by
  apply decodeReferencedElements (by native_decide) rfl rfl
  intro j hlo hhi
  rw [show child multiRequestPlan .element = multiRequestRowPlan by native_decide,
    multiRequestElement_decode cd base j (by omega) hsize]
  simp only [retainFailure,show multiRequestRowPlan.deferErrors.contains [] = true from rfl,
    if_true,multiRequestValue]

end Benchmarks.EAS.EAS
