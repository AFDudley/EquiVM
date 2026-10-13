import Benchmarks.EAS.EAS.CalldataArrayExtent
import Benchmarks.EAS.Attester.NestedBounds
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES calldataArrayExtent_signed to any bounded static element stride.
theorem calldataArrayExtent_signed_stride {cd : ByteArray} {header : UInt256} {stride : Nat}
    (hsize : cd.size < 2^255)
    (hprod : stride*(calldataWord cd header.toNat).toNat < 2^128)
    (hend : UInt256.gt ((header+UInt256.ofNat 32)+UInt256.ofNat (stride*(calldataWord cd header.toNat).toNat))
      (UInt256.ofNat cd.size) = ⟨0⟩) :
    UInt256.sgt ((UInt256.ofNat 32)+header)
      (UInt256.sub (UInt256.ofNat cd.size) (UInt256.ofNat (stride*(calldataWord cd header.toNat).toNat))) = ⟨0⟩ := by
  have hc := calldataArrayExtent_stride (by omega) hprod hend
  rw [u256_add_comm (UInt256.ofNat 32),ofNat_sub_words (by omega) (by change cd.size < 2^256; omega)]
  have hn : (UInt256.ofNat (cd.size-stride*(calldataWord cd header.toNat).toNat)).toNat =
      cd.size-stride*(calldataWord cd header.toNat).toNat := ulit_toNat' _ (by change _ < 2^256; omega)
  exact sgt_zero_low (by omega) (by rw [hn]; omega) (by rw [hn]; omega)

end Benchmarks.EAS.EAS
