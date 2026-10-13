import Benchmarks.EAS.EAS.OneRequestMemory
import Benchmarks.EAS.EAS.CopyRequestCall
import Benchmarks.EAS.EAS.AttestDecode
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def attestPublicInitialMemory : ByteArray := Reasoning.Theory.writeWord ByteArray.empty 64 (UInt256.ofNat 224)
def attestPublicArrayMemory : ByteArray := oneRequestArrayMemory attestPublicInitialMemory (UInt256.ofNat 224)
def attestPublicCopiedMemory (cd : ByteArray) (root : UInt256) : ByteArray :=
  requestCopyMemory attestPublicArrayMemory cd (attestRequestData cd root) (UInt256.ofNat 480)
def attestPublicInputMemory (cd : ByteArray) (root : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (attestPublicCopiedMemory cd root) 256 (UInt256.ofNat 480)

theorem attestPublicArrayMemory_facts :
    480 ≤ attestPublicArrayMemory.size ∧
    memLoad (UInt256.ofNat 224) attestPublicArrayMemory = ⟨1⟩ ∧
    memLoad (UInt256.ofNat 64) attestPublicArrayMemory = UInt256.ofNat 480 ∧
    memLoad (UInt256.ofNat 96) attestPublicArrayMemory = ⟨0⟩ := by native_decide

theorem attestPublicInputMemory_view (cd : ByteArray) (root : UInt256)
    (hsize : cd.size < 2^255+4) (hd : requestDataValid cd (attestRequestData cd root))
    (hv : copyRequestValid 480 (requestDataRecord cd (attestRequestData cd root)).data.size) :
    let heap := copyRequestNext 480 (requestDataRecord cd (attestRequestData cd root)).data.size
    AttestationRequestArrayRegion (attestPublicInputMemory cd root) (UInt256.ofNat 224)
      [requestDataRecord cd (attestRequestData cd root)] 224 heap ∧
    memLoad (UInt256.ofNat 64) (attestPublicInputMemory cd root) = UInt256.ofNat heap ∧
    memLoad (UInt256.ofNat 96) (attestPublicInputMemory cd root) = ⟨0⟩ := by
  let final := attestPublicCopiedMemory cd root
  have hm := requestCopyMemory_views attestPublicArrayMemory cd (attestRequestData cd root) (UInt256.ofNat 480)
    (by decide) (by decide) hsize hd hv
  have hc : 480 ≤ final.size := le_trans attestPublicArrayMemory_facts.1 hm.1.size
  have hlen : memLoad (UInt256.ofNat 224) final = ⟨1⟩ :=
    (memLoad_of_prefix hm.1 _ (by decide) (by decide) (by have := attestPublicArrayMemory_facts.1; change 256 ≤ _; omega)).trans
      attestPublicArrayMemory_facts.2.1
  have hzero : memLoad (UInt256.ofNat 96) final = ⟨0⟩ :=
    (memLoad_of_prefix hm.1 _ (by decide) (by decide) (by have := attestPublicArrayMemory_facts.1; change 128 ≤ _; omega)).trans
      attestPublicArrayMemory_facts.2.2.2
  have hb : copyRequestNext 480 (requestDataRecord cd (attestRequestData cd root)).data.size < UInt256.size := by
    have := hv.2.2.1
    change _ < 2^256
    omega
  have hreg := requestSingleton_set (array := UInt256.ofNat 224) (lower := 224)
    (by decide) (le_refl _) (by decide) (by native_decide) (by change 288 ≤ final.size; omega) hlen
    hm.2.1 hm.2.2.2.1 (le_of_eq hm.2.2.2.2.1) hb
  refine ⟨hreg,?_,?_⟩
  · exact (memLoad_write_below final 256 (UInt256.ofNat 64) (UInt256.ofNat 480) (by decide)
      (by change 96 ≤ final.size; omega)).trans hm.2.2.1
  · exact (memLoad_write_below final 256 (UInt256.ofNat 96) (UInt256.ofNat 480) (by decide)
      (by change 128 ≤ final.size; omega)).trans hzero

end Benchmarks.EAS.EAS
