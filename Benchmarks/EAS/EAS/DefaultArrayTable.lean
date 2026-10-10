import Benchmarks.EAS.EAS.DefaultArrayAllocate
import Benchmarks.EAS.EAS.StructSlotsViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def defaultArrayPointers (heap : UInt256) (len : Nat) : List UInt256 :=
  (List.range len).map fun i => UInt256.ofNat (heap.toNat+32+32*len+320*i)

@[simp] theorem defaultArrayPointers_length (heap : UInt256) (len : Nat) :
    (defaultArrayPointers heap len).length = len := by
  simp only [defaultArrayPointers,List.length_map,List.length_range]

theorem defaultArrayMemory_view (mem : ByteArray) (heap : UInt256) (len : Nat)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1) (hl : len ≤ 2^64-1) :
    let next := allocateNext heap.toNat (32+352*len)
    let final := defaultArrayMemory mem heap len
    MemoryPrefix mem final heap.toNat ∧ next ≤ final.size ∧
      memLoad (UInt256.ofNat 64) final = UInt256.ofNat next ∧
      WordArrayMemoryView final heap (defaultArrayPointers heap len) next := by
  dsimp only
  let header := arrayAllocationHeaderMemory mem heap len
  let start := heap.toNat+32+32*len
  let next := heap.toNat+32+352*len
  let final := defaultArrayMemory mem heap len
  rw [allocateNext_recordArray hh hl]
  change MemoryPrefix mem final heap.toNat ∧ next ≤ final.size ∧
    memLoad (UInt256.ofNat 64) final = UInt256.ofNat next ∧
    WordArrayMemoryView final heap (defaultArrayPointers heap len) next
  have hheadsize : header.size = max mem.size (heap.toNat+32) := by
    simp only [header,arrayAllocationHeaderMemory,writeWord_sparse_size]
    omega
  have hheadfree : memLoad (UInt256.ofNat 64) header = UInt256.ofNat start := by
    change memLoad (UInt256.ofNat 64)
      (writeWordSequence (Reasoning.Theory.writeWord mem 64
        (UInt256.ofNat (allocateNext heap.toNat (32+32*len)))) heap.toNat [UInt256.ofNat len]) = _
    rw [writeWordSequence_setFree_load64 _ _ _ _ hlo,allocateNext_wordArray hh hl]
  have hheadlength : memLoad heap header = UInt256.ofNat len :=
    mloadWordValue_of_readWithPadding (by rw [hheadsize]; omega) (writeWord_sparse_read_back _ _ _)
  have hfullsize : next ≤ final.size := by
    cases len with
    | zero =>
      change heap.toNat+32+352*0 ≤ header.size
      rw [hheadsize]
      omega
    | succ n =>
      change heap.toNat+32+352*(n+1) ≤
        (structSlotsMemory header (heap.toNat+32+32*(n+1)) (heap.toNat+32) defaultAttestationWords (n+1)).size
      rw [structSlotsMemory_size (by omega) (by omega) (by decide) _ (by omega)]
      change heap.toNat+32+352*(n+1) ≤ max header.size (heap.toNat+32+32*(n+1)+320*(n+1))
      omega
  have hp := structSlotsMemory_prefix header start (heap.toNat+32) (heap.toNat+32)
    defaultAttestationWords (by dsimp only [start]; omega) (le_refl _) len
  have hb : next < UInt256.size := by dsimp only [next]; change heap.toNat+32+352*len < 2^256; omega
  refine ⟨?_,hfullsize,?_,hlo,?_,?_,?_,?_⟩
  · exact ((memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ heap.toNat _ _ (Or.inl (le_refl _)))).trans (hp.mono (by omega))
  · have hf := structSlotsMemory_freePtr (mem := header) (free := start) (slot := heap.toNat+32)
      (fields := defaultAttestationWords) (by dsimp only [start]; omega) (by omega) hheadfree len
    change memLoad (UInt256.ofNat 64) final = UInt256.ofNat (start+320*len) at hf
    convert hf using 1
    congr 1
    dsimp only [next,start]
    omega
  · rw [defaultArrayPointers_length]
    dsimp only [next]
    omega
  · rw [defaultArrayPointers_length]
    have hle : heap.toNat+32+32*len ≤ next := by dsimp only [next]; omega
    exact le_trans hle hfullsize
  · rw [defaultArrayPointers_length]
    exact (memLoad_of_prefix hp heap hlo (le_refl _) (by rw [hheadsize]; omega)).trans hheadlength
  · rw [defaultArrayPointers_length]
    apply List.ext_getElem
    · rw [memoryWords_length,defaultArrayPointers_length]
    · intro i hi hj
      have hi' : i < len := by simpa only [memoryWords_length] using hi
      rw [memoryWords_get _ _ _ _ hi']
      simp only [defaultArrayPointers,List.getElem_map,List.getElem_range]
      exact structSlotsMemory_slot header start (heap.toNat+32) defaultAttestationWords len i
        (by omega) (le_refl _) (by dsimp only [next] at hb; omega) hi'

end Benchmarks.EAS.EAS
