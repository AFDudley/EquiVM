import Benchmarks.Morpho.MetaMorphoV1_1.MulticallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.MulticallCalldataRuntime

/-! Preserve existing results through input copying and add a returned byte buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem MulticallMemory.copy {mem cd : ByteArray} {ptr base : UInt256} {i : Nat}
    {results : List ByteArray} (h : MulticallMemory mem ptr results)
    (hsize : cd.size < 2 ^ 255) (hv : bytesArrayAccessValid cd base i)
    (hf : allocationFits ptr (UInt256.ofNat (32 + (bytesTailData cd (bytesArrayHead cd base i)).size))) :
    MulticallMemory (multicallElementMemory mem cd ptr base i)
      (bytesAllocPtr ptr (bytesTailData cd (bytesArrayHead cd base i)).size) results := by
  have hl : (calldataWord cd (bytesArrayHead cd base i).toNat).toNat < 2 ^ 64 := by
    have hlen := hv.2.1
    change _ ≤ 18446744073709551615 at hlen
    omega
  have hb := bytesTailValid_copyBounds hsize hv.2
  have hn := hf
  rw [allocationFits, nextCursor_bytesAlloc] at hn
  apply h.preserve (calldataBytesMemory_bytePrefix _ _ _ _ _ h.bound hl hb) hn.1 hn.2
  rw [bytesTailData_size]
  exact calldataBytesMemory_free _ _ _ _ _ h.bound hl (by have := h.lower; omega) hb

theorem multicallElementMemory_buffer {mem cd : ByteArray} {ptr base : UInt256} {i : Nat}
    (hp : ptr.toNat < 2 ^ 64) (hlo : 96 ≤ ptr.toNat)
    (hsize : cd.size < 2 ^ 255) (hv : bytesArrayAccessValid cd base i) :
    StringBuffer (multicallElementMemory mem cd ptr base i) ptr.toNat
      (bytesTailData cd (bytesArrayHead cd base i)) := by
  rw [bytesTailData_eq_extract hsize hv.2]
  exact calldataBytesMemory_buffer _ _ _ _ _ hp
    (by have hlen := hv.2.1; change _ ≤ 18446744073709551615 at hlen; omega) hlo
    (bytesTailValid_copyBounds hsize hv.2)

theorem callReturnFits_size {ptr : UInt256} {out : ByteArray} (hf : callReturnFits ptr out) :
    out.size < 2 ^ 64 := by
  rcases hf with hz | ⟨hs, _⟩
  · rw [hz]; decide
  · exact hs

theorem callReturnPointer_end {ptr : UInt256} {out : ByteArray}
    (hp : ptr.toNat < 2 ^ 64) (hlo : 128 ≤ ptr.toNat) (hf : callReturnFits ptr out) :
    (callReturnPointer ptr out).toNat + 32 + out.size ≤ (callReturnCursor ptr out).toNat := by
  by_cases hz : out.size = 0
  · simp only [callReturnPointer, callReturnCursor, hz, if_true]
    change 96 + 32 + 0 ≤ ptr.toNat
    omega
  · have hs := callReturnFits_size hf
    simp only [callReturnPointer, callReturnCursor, hz, if_false]
    rw [bytesAllocPtr_toNat (by change _ ≤ 2 ^ 200; omega)]
    omega

def multicallStoreResultMemory (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (i : Nat) : ByteArray :=
  writeWord (callReturnMemory mem ptr out) (160 + 32 * i) (callReturnPointer ptr out)

theorem MulticallMemory.storeReturn {mem out : ByteArray} {ptr : UInt256} {i : Nat}
    {results : List ByteArray} (h : MulticallMemory mem ptr results)
    (hi : i < results.length) (hf : callReturnFits ptr out) :
    MulticallMemory (multicallStoreResultMemory mem ptr out i)
      (callReturnCursor ptr out) (results.set i out) := by
  have hn := callReturnCursor_bound ptr out h.bound hf
  have hpres := h.preserve (callReturnMemory_bytePrefix mem ptr out) hn.1 hn.2
    (callReturnMemory_free mem ptr out (by have := h.lower; omega) h.free)
  apply hpres.storeResult hi
  · unfold callReturnPointer
    split
    · exact .inl rfl
    · exact .inr h.lower
  · exact callReturnPointer_end h.bound (by have := h.lower; omega) hf
  · exact callReturnFits_size hf
  · exact callReturnMemory_buffer mem ptr out (by have := h.size; omega) h.zero

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
