import Benchmarks.EAS.EAS.RecordValuesStore
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def recordResultPtr (site : UIDSite) (mem : ByteArray) : UInt256 :=
  match site with
  | .single _ _ _ _ _ _ s7 _ => s7
  | .many .. => memLoad (UInt256.ofNat 128) mem

theorem recordUIDsPtr_preserve {before after : ByteArray} {limit : Nat} (site : UIDSite)
    (hp : MemoryPrefix before after limit) (hlo : 160 ≤ limit) (hin : 160 ≤ before.size)
    (hrlo : 96 ≤ (recordResultPtr site before).toNat)
    (hrhi : (recordResultPtr site before).toNat+64 ≤ limit)
    (hrin : (recordResultPtr site before).toNat+64 ≤ before.size) (hb : limit < UInt256.size) :
    recordUIDsPtr site after = recordUIDsPtr site before := by
  have hr : recordResultPtr site after = recordResultPtr site before := by
    cases site with
    | single _ _ _ _ _ _ _ _ => rfl
    | many _ _ _ _ _ _ => exact memLoad_of_prefix hp _ (by decide) hlo hin
  have heq (mem : ByteArray) : recordUIDsPtr site mem = memLoad (recordResultPtr site mem+UInt256.ofNat 32) mem := by
    cases site <;> rfl
  rw [heq,heq,hr]
  have he : (recordResultPtr site before+UInt256.ofNat 32).toNat = (recordResultPtr site before).toNat+32 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  exact memLoad_of_prefix hp _ (by rw [he]; omega) (by rw [he]; omega) (by rw [he]; omega)

end Benchmarks.EAS.EAS
