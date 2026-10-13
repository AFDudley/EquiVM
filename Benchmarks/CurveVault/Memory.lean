import Benchmarks.CurveVault.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: a Vyper mapping preimage fits in already allocated scratch memory.
theorem vyperHashMem_size (base key : UInt256) (mem : ByteArray) (hmem : 64 ≤ mem.size) :
    (wordAt0Mem base (wordAt32Mem key mem)).size = mem.size := by
  rw [wordAt0Mem_size_of_ge64 _ (by rw [wordAt32Mem_size_of_ge_64 _ hmem]; exact hmem),
    wordAt32Mem_size_of_ge_64 _ hmem]

-- GENERALIZES Reasoning.Theory.wordAt0Mem_wordAt32Mem_vyperMappingSlot:
-- expose the canonical-address bridge in the bytecode summary's keccakWord notation.
theorem vyperHashMem_address (base key : UInt256) (mem : ByteArray)
    (hmem : 64 ≤ mem.size) (hcanon : key.toNat < EVM.addressModulus) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem base (wordAt32Mem key mem)) =
      vyperMappingSlot base (.address (AccountAddress.ofNat key.toNat)) := by
  change UInt256.ofNat (fromByteArrayBigEndian
    (KEC ((wordAt0Mem base (wordAt32Mem key mem)).readWithPadding 0 64))) = _
  rw [wordAt0Mem_wordAt32Mem_read0_64 _ _ hmem]
  exact vyperMappingSlot_hash_address _ key hcanon

-- LIBRARY CANDIDATE: a Vyper mapping preimage preserves subsequent memory words.
theorem memLoad_vyperHashMem (base key : UInt256) (mem : ByteArray) (off : Nat)
    (hafter : 64 ≤ off) (hin : off + 32 ≤ mem.size) (hoff : off < UInt256.size) :
    memLoad (UInt256.ofNat off) (wordAt0Mem base (wordAt32Mem key mem)) =
      memLoad (UInt256.ofNat off) mem := by
  have hmem : 64 ≤ mem.size := by omega
  change memLoad (UInt256.ofNat off)
    (base.toByteArray.write 0 (wordAt32Mem key mem) 0 32) = _
  rw [memLoad_above_write _ _ 0 off (by rw [toByteArray_size]) (by omega) (by omega)
    (by rw [wordAt32Mem_size_of_ge_64 key hmem]; exact hin) hoff]
  exact memLoad_above_write _ _ 32 off (by rw [toByteArray_size]) (by omega) hafter hin hoff

-- GENERALIZES Reasoning.Theory.MemoryPrefix: arbitrary lower and upper bounds
-- and the EVM word-loading notation used by Vyper's block summaries.
structure WordMemoryRange (before after : ByteArray) (lo hi : Nat) : Prop where
  size : before.size ≤ after.size
  load : ∀ off, lo ≤ off → off + 32 ≤ hi → off + 32 ≤ before.size → off < UInt256.size →
    memLoad (UInt256.ofNat off) after = memLoad (UInt256.ofNat off) before

theorem WordMemoryRange.refl (mem : ByteArray) (lo hi : Nat) : WordMemoryRange mem mem lo hi :=
  ⟨le_refl _, fun _ _ _ _ _ => rfl⟩

theorem WordMemoryRange.trans {a b c : ByteArray} {lo hi : Nat}
    (hab : WordMemoryRange a b lo hi) (hbc : WordMemoryRange b c lo hi) :
    WordMemoryRange a c lo hi := by
  refine ⟨le_trans hab.size hbc.size, fun off hlo hhi hin hoff => ?_⟩
  rw [hbc.load off hlo hhi (le_trans hin hab.size) hoff, hab.load off hlo hhi hin hoff]

theorem WordMemoryRange.mono {a b : ByteArray} {lo hi lo' hi' : Nat}
    (h : WordMemoryRange a b lo hi) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    WordMemoryRange a b lo' hi' :=
  ⟨h.size, fun off low high hin hoff => h.load off (le_trans hlo low) (le_trans high hhi) hin hoff⟩

theorem wordMemoryRange_write (mem : ByteArray) (word : UInt256) (off lo hi : Nat)
    (hgap : off - mem.size < USize.size) (hdisj : hi ≤ off ∨ off + 32 ≤ lo) :
    WordMemoryRange mem (word.toByteArray.write 0 mem off 32) lo hi := by
  refine ⟨?_, fun read hlo hhi hin hoff => ?_⟩
  · change mem.size ≤ (writeWord mem off word).size
    rw [writeWord_size mem off word hgap]
    exact Nat.le_max_left _ _
  · rcases hdisj with hbefore | hafter
    · exact memLoad_below_write word mem off read hin (le_trans hhi hbefore) hgap hoff
    · exact memLoad_above_write _ _ off read (by rw [toByteArray_size])
        (by omega) (by omega) hin hoff

-- LIBRARY CANDIDATE: hashing a Vyper mapping key preserves every later allocated word.
theorem wordMemoryRange_vyperHash (mem : ByteArray) (base key : UInt256) (lo hi : Nat)
    (hlo : 64 ≤ lo) :
    WordMemoryRange mem (wordAt0Mem base (wordAt32Mem key mem)) lo hi := by
  have hgap (off : Nat) (h : off ≤ 32) (m : ByteArray) : off - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize off (by omega))
  exact (wordMemoryRange_write mem key 32 lo hi (hgap _ (by omega) _) (Or.inr (by omega))).trans
    (wordMemoryRange_write _ base 0 lo hi (hgap _ (by omega) _) (Or.inr (by omega)))

theorem wordMemoryRange_copy (src mem : ByteArray) (srcOff dest len lo hi : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hdisj : hi ≤ dest ∨ dest + len ≤ lo) :
    WordMemoryRange mem (src.write srcOff mem dest len) lo hi := by
  have hs : mem.size ≤ (src.write srcOff mem dest len).size := by
    rw [copyWindow_size src mem srcOff dest len hpos hsrc hdest]
    omega
  refine ⟨hs, fun off hlo hhi hin hoff => ?_⟩
  have hbytes := copyWindow_read_preserved src mem srcOff dest len off hpos hsrc hdest hin
    (by rcases hdisj with h | h <;> omega)
  unfold memLoad
  rw [ulit_toNat' off hoff, if_neg (by omega), if_neg (by omega), hbytes]
-- GENERALIZES Reasoning.Theory.copyWindow_read_word to EVM word loads.
theorem memLoad_copyWindow (src mem : ByteArray) (srcOff dest len off : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hwithin : off + 32 ≤ len)
    (hd : dest + off < UInt256.size) (hs : srcOff + off < UInt256.size) :
    memLoad (UInt256.ofNat (dest + off)) (src.write srcOff mem dest len) =
      memLoad (UInt256.ofNat (srcOff + off)) src := by
  have hsize := copyWindow_size src mem srcOff dest len hpos hsrc hdest
  unfold memLoad
  rw [ulit_toNat' _ hd, ulit_toNat' _ hs, if_neg (by omega), if_neg (by omega),
    copyWindow_read_word src mem srcOff dest len off hpos hsrc hdest hwithin]
end Benchmarks.CurveVault
