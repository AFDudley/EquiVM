import Benchmarks.Morpho.MetaMorphoV1_1.CalldataBytesMemory
import Benchmarks.EAS.Attester.UnboundedMemory

/-! Preservation of allocated byte windows, including final partial words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: MemoryPrefix strengthened to preserve arbitrary byte windows.
structure ByteMemoryPrefix (before after : ByteArray) (limit : Nat) : Prop where
  size : before.size ≤ after.size
  read : ∀ off len, 96 ≤ off → off + len ≤ limit → off + len ≤ before.size →
    after.readWithPadding off len = before.readWithPadding off len

theorem ByteMemoryPrefix.refl (mem : ByteArray) (limit : Nat) :
    ByteMemoryPrefix mem mem limit := ⟨le_refl _, fun _ _ _ _ _ ↦ rfl⟩

theorem ByteMemoryPrefix.trans {a b c : ByteArray} {limit : Nat}
    (hab : ByteMemoryPrefix a b limit) (hbc : ByteMemoryPrefix b c limit) :
    ByteMemoryPrefix a c limit :=
  ⟨le_trans hab.size hbc.size, fun off len hlo hhi hin ↦
    (hbc.read off len hlo hhi (le_trans hin hab.size)).trans (hab.read off len hlo hhi hin)⟩

theorem ByteMemoryPrefix.mono {a b : ByteArray} {lo hi : Nat}
    (h : ByteMemoryPrefix a b hi) (hle : lo ≤ hi) : ByteMemoryPrefix a b lo :=
  ⟨h.size, fun off len hlo hhi hin ↦ h.read off len hlo (le_trans hhi hle) hin⟩

theorem ByteMemoryPrefix.words {a b : ByteArray} {limit : Nat}
    (h : ByteMemoryPrefix a b limit) : MemoryPrefix a b limit :=
  ⟨h.size, fun off hlo hhi hin ↦ h.read off 32 hlo hhi hin⟩

theorem byteMemoryPrefix_writeWord (mem : ByteArray) (off limit : Nat) (word : UInt256)
    (hdisj : limit ≤ off ∨ off + 32 ≤ 96) :
    ByteMemoryPrefix mem (writeWord mem off word) limit := by
  refine ⟨by rw [writeWord_sparse_size]; omega, fun read len hlo hhi hin ↦ ?_⟩
  exact writeWord_sparse_read_preserved_unbounded mem off read len word hin
    (hdisj.imp (fun h ↦ by omega) (fun h ↦ by omega))

-- GENERALIZES copyWindow_read_preserved to arbitrary possibly empty windows below the copy.
theorem copyWindow_read_before_unbounded (src mem : ByteArray) (srcOff dest len read count : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hin : read + count ≤ mem.size) (hbelow : read + count ≤ dest) :
    (src.write srcOff mem dest len).readWithPadding read count =
      mem.readWithPadding read count := by
  by_cases hz : count = 0
  · simp only [hz, byteArray_readWithPadding_zero]
  by_cases hl : len = 0
  · rw [hl, byteArray_write_len_zero]
  have hp : (mem.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  have hs : (src.extract srcOff (srcOff + len)).size = len := by
    rw [ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega)
      (by rw [copyWindow_size src mem srcOff dest len hl hsrc hdest]; omega),
    readWithPadding_eq_extract_unbounded _ _ _ (by omega) hin,
    copyWindow_eq src mem srcOff dest len hl hsrc hdest,
    extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hp, hs]; omega),
    extract_append_left _ _ _ _ (by rw [hp]; omega), extract_extract_BA]
  congr 1 <;> omega

theorem byteMemoryPrefix_copy (src mem : ByteArray) (srcOff dest len limit : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size) (hbelow : limit ≤ dest) :
    ByteMemoryPrefix mem (src.write srcOff mem dest len) limit := by
  refine ⟨?_, fun read count _ hhi hin ↦
    copyWindow_read_before_unbounded _ _ _ _ _ _ _ hsrc hdest hin (by omega)⟩
  by_cases hz : len = 0
  · rw [hz, byteArray_write_len_zero]
  · rw [copyWindow_size _ _ _ _ _ hz hsrc hdest]; omega

theorem calldataBytesMemory_bytePrefix (mem cd : ByteArray) (ptr start len : UInt256)
    (hp : ptr.toNat < 2 ^ 64) (hl : len.toNat < 2 ^ 64)
    (hsrc : start.toNat + len.toNat ≤ cd.size) :
    ByteMemoryPrefix mem (calldataBytesMemory mem cd ptr start len) ptr.toNat := by
  rw [calldataBytesMemory_normalize mem cd ptr start len hp hl]
  exact (byteMemoryPrefix_writeWord mem 64 ptr.toNat _ (.inr (by decide))).trans
    ((byteMemoryPrefix_writeWord _ ptr.toNat ptr.toNat len (.inl (le_refl _))).trans
      ((byteMemoryPrefix_copy cd _ start.toNat (ptr.toNat + 32) len.toNat ptr.toNat
        hsrc (by simp only [writeWord_sparse_size]; omega) (by omega)).trans
        (byteMemoryPrefix_writeWord _ _ ptr.toNat _ (.inl (by omega)))))

theorem callReturnMemory_bytePrefix (mem : ByteArray) (ptr : UInt256) (out : ByteArray) :
    ByteMemoryPrefix mem (callReturnMemory mem ptr out) ptr.toNat := by
  unfold callReturnMemory
  split
  · exact .refl _ _
  · exact (byteMemoryPrefix_writeWord mem 64 ptr.toNat _ (.inr (by decide))).trans
      ((byteMemoryPrefix_writeWord _ ptr.toNat ptr.toNat _ (.inl (le_refl _))).trans
        (byteMemoryPrefix_copy out _ 0 (ptr.toNat + 32) out.size ptr.toNat
          (by omega) (by simp only [writeWord_sparse_size]; omega) (by omega)))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
