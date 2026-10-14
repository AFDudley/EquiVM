import Benchmarks.EAS.EAS.RequestDecode
import Benchmarks.EAS.EAS.CopyRequestEVM
import Benchmarks.EAS.EAS.CopyRequestSource
import Benchmarks.EAS.EAS.CalldataPayload
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem requestDataRecord_size (cd : ByteArray) (src : UInt256) :
    (requestDataRecord cd src).data.size = (requestDataLength cd src).toNat :=
  calldataRead_size _ _ _

theorem requestCopyRunValid_iff {cd : ByteArray} {src heap : UInt256}
    (hd : requestDataValid cd src) :
    requestCopyRunValid cd src (UInt256.ofNat cd.size) heap ↔
      copyRequestValid heap.toNat (requestDataRecord cd src).data.size := by
  rw [requestDataRecord_size]
  constructor
  · rintro ⟨_,ha,_,hb⟩
    have hn : (UInt256.ofNat (allocateNext heap.toNat 192)).toNat = allocateNext heap.toNat 192 :=
      ulit_toNat' _ (by change _ < 2^256; omega)
    rcases hb with ⟨_,hl,halloc,_⟩
    change (allocateNext (UInt256.ofNat (allocateNext heap.toNat 192)).toNat
        (bytesAllocation (requestDataLength cd src).toNat) ≤ 2^64-1 ∧
      (UInt256.ofNat (allocateNext heap.toNat 192)).toNat ≤
        allocateNext (UInt256.ofNat (allocateNext heap.toNat 192)).toNat
          (bytesAllocation (requestDataLength cd src).toNat)) at halloc
    rw [hn] at halloc
    exact ⟨ha,hl,halloc⟩
  · rintro ⟨ha,hl,halloc⟩
    have hn : (UInt256.ofNat (allocateNext heap.toNat 192)).toNat = allocateNext heap.toNat 192 :=
      ulit_toNat' _ (by change _ < 2^256; omega)
    refine ⟨hd.1,ha,hd.2.1,hd.2.2.1,hl,?_,hd.2.2.2.2⟩
    change (allocateNext (UInt256.ofNat (allocateNext heap.toNat 192)).toNat
        (bytesAllocation (requestDataLength cd src).toNat) ≤ 2^64-1 ∧
      (UInt256.ofNat (allocateNext heap.toNat 192)).toNat ≤
        allocateNext (UInt256.ofNat (allocateNext heap.toNat 192)).toNat
          (bytesAllocation (requestDataLength cd src).toNat))
    rw [hn]
    exact halloc

end Benchmarks.EAS.EAS
