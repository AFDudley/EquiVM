import Reasoning.BytecodePatching
import Reasoning.Reach

/-!
# Vyper immutable runtime suffixes

Vyper 0.4.3 allocates immutables in a code section appended by the constructor.
Offsets below are relative to that section, as reported by `code_layout`.
Each supported scalar occupies one 32-byte slot. `bytesN` values use Vyper's
left-aligned in-memory representation; numeric values and addresses use the
ordinary big-endian word representation.
-/

namespace Reasoning.VyperImmutables

open Solm
open Reasoning.Theory

structure Slot where
  name : String
  offset : Nat
  length : Nat
  deriving Repr, DecidableEq

structure Layout where
  slots : List Slot
  size : Nat
  deriving Repr

/-- Scalar representation of a Solm value in Vyper's immutable code section. -/
def scalarBytes? (v : Value) : Option ByteArray :=
  match v with
  | .fixedBytes _ bs =>
      if bs.length ≤ 32 then
        some (ByteArray.mk ((bs ++ List.replicate (32 - bs.length) 0).toArray))
      else none
  | _ => (valueToWord v).map (fun w => w.toByteArray)

/-- Turn a scalar Solm immutable into the word used by runtime summaries.
    For `bytesN`, `scalarBytes?` has already placed the bytes on the left. -/
def wordsOf (imms : Store) (name : String) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray
    (((imms.get? name).bind scalarBytes?).getD (ByteArray.zeroes 32))

/-- One compiler-reported slot and its constructor value. -/
def Slot.patch? (slot : Slot) (imms : Store) : Option (Nat × ByteArray) := do
  if slot.length != 32 then none else
  let v ← imms.get? slot.name
  let encoded ← scalarBytes? v
  return (slot.offset, encoded)

def Layout.patches? (layout : Layout) (imms : Store) : Option (List (Nat × ByteArray)) :=
  layout.slots.mapM (·.patch? imms)

/-- Encode the suffix from the compiler's slot layout and a valuation. -/
def Layout.suffix? (layout : Layout) (imms : Store) : Option ByteArray := do
  let patches ← layout.patches? imms
  patchRuntime (ByteArray.zeroes layout.size) patches

/-- Scalar-only word valuation of a compiler-reported immutable layout.
    Compound immutable entries require a separate flattening rule. -/
def Layout.suffixWords (layout : Layout) (words : String → Ethereum.UInt256) : ByteArray :=
  (patchRuntime (ByteArray.zeroes layout.size)
    (layout.slots.map (fun slot => (slot.offset, Ethereum.UInt256.toByteArray (words slot.name))))).getD
    (ByteArray.zeroes layout.size)

theorem Layout.suffixWords_size (layout : Layout) (words : String → Ethereum.UInt256) :
    (layout.suffixWords words).size = layout.size := by
  unfold Layout.suffixWords
  cases hpatch : patchRuntime (ByteArray.zeroes layout.size)
      (layout.slots.map (fun slot =>
        (slot.offset, Ethereum.UInt256.toByteArray (words slot.name)))) with
  | none => simp [ByteArray_zeroes_size]
  | some out =>
      simpa [hpatch, ByteArray_zeroes_size] using patchRuntime_size_eq hpatch

/-- A compiler-reported scalar slot reads back as its word valuation. The
    patch witness records that the scalar layout fits the reported suffix. -/
theorem Layout.suffixWords_read_slot {layout : Layout}
    {words : String → Ethereum.UInt256} {name : String} {offset : Nat}
    {pre post : List (Nat × ByteArray)}
    (hslots : layout.slots.map (fun slot =>
      (slot.offset, Ethereum.UInt256.toByteArray (words slot.name))) =
      pre ++ (offset, Ethereum.UInt256.toByteArray (words name)) :: post)
    (hbound : offset + 32 ≤ layout.size)
    (hpost : ∀ p ∈ post, offset + 32 ≤ p.1 ∨ p.1 + 32 ≤ offset)
    (hpatch : ∃ suffix, patchRuntime (ByteArray.zeroes layout.size)
      (layout.slots.map (fun slot =>
        (slot.offset, Ethereum.UInt256.toByteArray (words slot.name)))) = some suffix) :
    (layout.suffixWords words).readWithPadding offset 32 =
      Ethereum.UInt256.toByteArray (words name) := by
  obtain ⟨suffix, hsuffix⟩ := hpatch
  have hsize : suffix.size = layout.size := by
    simpa [ByteArray_zeroes_size] using patchRuntime_size_eq hsuffix
  simp only [Layout.suffixWords, hsuffix, Option.getD_some]
  rw [readWithPadding_eq_extract suffix offset (by omega)]
  exact patchRuntime_extract_patch (by simp [toByteArray_size]) hpost (by simpa [hslots] using hsuffix)

theorem Layout.suffix_size_of_some {layout : Layout} {imms : Store}
    {suffix : ByteArray} (hsuffix : layout.suffix? imms = some suffix) :
    suffix.size = layout.size := by
  unfold Layout.suffix? at hsuffix
  cases hpatches : layout.patches? imms with
  | none => simp [hpatches] at hsuffix
  | some patches =>
      simp only [hpatches] at hsuffix
      simpa [ByteArray_zeroes_size] using patchRuntime_size_eq hsuffix

/-- The corresponding deployed runtime, when all immutable values are supplied. -/
def Layout.deployed? (layout : Layout) (template : ByteArray) (imms : Store) : Option ByteArray :=
  (layout.suffix? imms).map (template ++ ·)

/-- Total runtime function for refinement statements. Well-typed constructor proofs
    should establish that `suffix?` succeeds; the zero suffix covers invalid stores. -/
def Layout.deployed (layout : Layout) (template : ByteArray) (imms : Store) : ByteArray :=
  template ++ (layout.suffix? imms).getD (ByteArray.zeroes layout.size)

theorem Layout.deployed_eq_of_suffix {layout : Layout} {template : ByteArray}
    {imms : Store} {suffix : ByteArray} (h : layout.suffix? imms = some suffix) :
    layout.deployed template imms = template ++ suffix := by
  simp [Layout.deployed, h]

/-- A slot in a successfully encoded suffix contains exactly its value, provided
    later slots do not overlap it. The patch split is convenient to prove from a
    generated `code_layout`, while the separation condition is arithmetic. -/
theorem Layout.suffix_read_slot {layout : Layout} {imms : Store} {suffix value : ByteArray}
    {pre post : List (Nat × ByteArray)} {offset : Nat}
    (hpatches : layout.patches? imms = some (pre ++ (offset, value) :: post))
    (hvalue : value.size = 32)
    (hbound : offset + 32 ≤ layout.size)
    (hpost : ∀ p ∈ post, offset + 32 ≤ p.1 ∨ p.1 + 32 ≤ offset)
    (hsuffix : layout.suffix? imms = some suffix) :
    suffix.readWithPadding offset 32 = value := by
  have hrun : patchRuntime (ByteArray.zeroes layout.size)
      (pre ++ (offset, value) :: post) = some suffix := by
    simpa [Layout.suffix?, hpatches] using hsuffix
  have hsize : suffix.size = layout.size := by
    simpa [ByteArray_zeroes_size] using patchRuntime_size_eq hrun
  rw [readWithPadding_eq_extract suffix offset (by omega)]
  exact patchRuntime_extract_patch hvalue hpost hrun

/-- The EVM reads a Vyper immutable from the appended section, at the
    compiler-reported code offset. -/
theorem Layout.runtime_read_slot {layout : Layout} {template : ByteArray}
    {imms : Store} {suffix value : ByteArray} {pre post : List (Nat × ByteArray)}
    {offset : Nat}
    (hpatches : layout.patches? imms = some (pre ++ (offset, value) :: post))
    (hvalue : value.size = 32)
    (hbound : offset + 32 ≤ layout.size)
    (hpost : ∀ p ∈ post, offset + 32 ≤ p.1 ∨ p.1 + 32 ≤ offset)
    (hsuffix : layout.suffix? imms = some suffix) :
    (template ++ suffix).readWithPadding (template.size + offset) 32 = value := by
  have hsize : suffix.size = layout.size := by
    have hrun : patchRuntime (ByteArray.zeroes layout.size)
        (pre ++ (offset, value) :: post) = some suffix := by
      simpa [Layout.suffix?, hpatches] using hsuffix
    simpa [ByteArray_zeroes_size] using patchRuntime_size_eq hrun
  rw [readWithPadding_eq_extract (template ++ suffix) (template.size + offset)
    (by rw [ByteArray.size_append, hsize]; omega)]
  rw [extract_append_right_window template suffix _ _ (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [show template.size + offset + 32 - template.size = offset + 32 by omega]
  rw [← readWithPadding_eq_extract suffix offset (by rw [hsize]; omega)]
  exact Layout.suffix_read_slot hpatches hvalue hbound hpost hsuffix

/-- Normalize a copy destination by zero extending memory up to `dest`.
    `ByteArray.write` performs this extension itself when needed. -/
theorem copy_padding (src mem : ByteArray) (srcOff dest len : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) :
    src.write srcOff mem dest len =
      src.write srcOff (mem ++ ByteArray.zeroes (dest - mem.size)) dest len := by
  by_cases hd : dest ≤ mem.size
  · have hz : ByteArray.zeroes (dest - mem.size) = ByteArray.empty := by
      rw [Nat.sub_eq_zero_of_le hd]
      exact zeroes_zero (by rfl)
    simp [hz]
  · have hmem : (mem ++ ByteArray.zeroes (dest - mem.size)).size = dest := by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega
    apply ByteArray.ext
    unfold ByteArray.write
    simp only [if_neg hpos, if_neg (show ¬ srcOff ≥ src.size by omega)]
    simp [hmem, ByteArray_zeroes_size,
      show min len (src.size - srcOff) = len by omega,
      show min mem.size (dest + len) = mem.size by omega,
      show mem.size - (dest + len) = 0 by omega,
      show dest - (dest + len) = 0 by omega]

/-- A complete 32-byte source window can be represented by its scalar bytes
    throughout the resulting memory, including when the copy extends it. -/
theorem copy_word_bytes (src mem bytes : ByteArray) (srcOff dest : Nat)
    (hsrc : srcOff + 32 ≤ src.size) (hbytes : bytes.size = 32)
    (hread : src.readWithPadding srcOff 32 = bytes) :
    src.write srcOff mem dest 32 = bytes.write 0 mem dest 32 := by
  have hwindow : src.extract srcOff (srcOff + 32) = bytes := by
    simpa only [readWithPadding_eq_extract src srcOff hsrc] using hread
  have hbytesWindow : bytes.extract 0 (0 + 32) = bytes := by
    simpa [hbytes] using byteArray_extract_self bytes
  rw [copy_padding src mem srcOff dest 32 (by decide) hsrc,
    copy_padding bytes mem 0 dest 32 (by decide) (by omega)]
  let padded := mem ++ ByteArray.zeroes (dest - mem.size)
  have hdest : dest ≤ padded.size := by
    dsimp [padded]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    omega
  rw [copyWindow_eq src padded srcOff dest 32 (by decide) hsrc hdest,
    copyWindow_eq bytes padded 0 dest 32 (by decide) (by omega) hdest]
  simp only [hwindow, hbytesWindow]

/-- Read any nonempty subwindow of a code copy, including when the write first
    extends memory. This is useful for array elements and struct fields. -/
theorem copy_window_read_range (src mem : ByteArray)
    (srcOff dest len off count : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size)
    (hcount : 0 < count) (hwithin : off + count ≤ len) :
    (src.write srcOff mem dest len).readWithPadding (dest + off) count =
      src.readWithPadding (srcOff + off) count := by
  rw [copy_padding src mem srcOff dest len hpos hsrc]
  let padded := mem ++ ByteArray.zeroes (dest - mem.size)
  have hdest : dest ≤ padded.size := by
    dsimp [padded]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    omega
  rw [readWithPadding_eq_extract_unbounded _ (dest + off) count hcount (by
      rw [copyWindow_size src padded srcOff dest len hpos hsrc hdest]
      omega)]
  rw [readWithPadding_eq_extract_unbounded src (srcOff + off) count hcount (by omega)]
  exact copyWindow_extract src padded srcOff dest len off count
    hpos hsrc hdest hwithin

/-- Read a word copied from code, including when the copy grows memory. -/
theorem copy_window_read_word (src mem : ByteArray) (srcOff dest len off : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size)
    (hwithin : off + 32 ≤ len) :
    (src.write srcOff mem dest len).readWithPadding (dest + off) 32 =
      src.readWithPadding (srcOff + off) 32 := by
  rw [copy_padding src mem srcOff dest len hpos hsrc]
  apply copyWindow_read_word src (mem ++ ByteArray.zeroes (dest - mem.size))
    srcOff dest len off hpos hsrc
  · rw [ByteArray.size_append, ByteArray_zeroes_size]
    omega
  · exact hwithin

/-- Reading the entire copied window gives the source window, even when
    `CODECOPY` extends memory before writing. -/
theorem copy_window_read (src mem : ByteArray) (srcOff dest len : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) :
    (src.write srcOff mem dest len).readWithPadding dest len =
      src.readWithPadding srcOff len := by
  rw [copy_padding src mem srcOff dest len hpos hsrc]
  let padded := mem ++ ByteArray.zeroes (dest - mem.size)
  have hdest : dest ≤ padded.size := by
    dsimp [padded]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    omega
  rw [readWithPadding_eq_extract_unbounded _ dest len (by omega) (by
      rw [copyWindow_size src padded srcOff dest len hpos hsrc hdest]
      omega)]
  rw [readWithPadding_eq_extract_unbounded src srcOff len (by omega) hsrc]
  exact copyWindow_extract src padded srcOff dest len 0 len hpos hsrc hdest (by omega)

/-- A return read of an already named scalar memory write yields its bytes. -/
theorem copy_word_read (word : Ethereum.UInt256) (mem : ByteArray) (dest : Nat) :
    (word.toByteArray.write 0 mem dest 32).readWithPadding dest 32 =
      word.toByteArray := by
  rw [copy_window_read word.toByteArray mem 0 dest 32 (by decide)
    (by rw [toByteArray_size])]
  rw [readWithPadding_eq_extract word.toByteArray 0 (by rw [toByteArray_size])]
  simpa [toByteArray_size] using byteArray_extract_self word.toByteArray

/-- Copying and returning the complete immutable section returns its suffix. -/
theorem Layout.codecopy_read_suffix {layout : Layout} {template mem suffix : ByteArray}
    (hsize : suffix.size = layout.size) (hpos : layout.size ≠ 0) (dest : Nat) :
    ((template ++ suffix).write template.size mem dest layout.size).readWithPadding
      dest layout.size = suffix := by
  rw [copy_window_read (template ++ suffix) mem template.size dest layout.size
    hpos (by rw [ByteArray.size_append, hsize])]
  rw [readWithPadding_eq_extract_unbounded _ template.size layout.size
    (by omega) (by rw [ByteArray.size_append, hsize])]
  rw [extract_append_right_window template suffix _ _ (by omega)]
  simpa [hsize] using (byteArray_extract_self suffix)

/-- A copy of the immutable section preserves any in-bounds byte window.
    The caller supplies the offset of a scalar, array element, length word,
    or struct field from the compiler's layout. -/
theorem Layout.codecopy_read_window {layout : Layout} {template mem suffix : ByteArray}
    (hsize : suffix.size = layout.size) (dest off count : Nat)
    (hcount : 0 < count) (hwithin : off + count ≤ layout.size) :
    ((template ++ suffix).write template.size mem dest layout.size).readWithPadding
      (dest + off) count = suffix.readWithPadding off count := by
  rw [copy_window_read_range (template ++ suffix) mem template.size dest
    layout.size off count (by omega) (by rw [ByteArray.size_append, hsize])
    hcount hwithin]
  rw [readWithPadding_eq_extract_unbounded (template ++ suffix)
    (template.size + off) count hcount (by rw [ByteArray.size_append, hsize]; omega)]
  rw [readWithPadding_eq_extract_unbounded suffix off count hcount (by rw [hsize]; omega)]
  rw [extract_append_right_window template suffix _ _ (by omega)]
  congr 1 <;> omega

/-- A 32-byte CODECOPY from a scalar immutable slot returns its word bytes. -/
theorem Layout.codecopy_read_scalar {layout : Layout} {template mem : ByteArray}
    {words : String → Ethereum.UInt256} {name : String} {offset dest : Nat}
    {pre post : List (Nat × ByteArray)}
    (hslots : layout.slots.map (fun slot =>
      (slot.offset, Ethereum.UInt256.toByteArray (words slot.name))) =
      pre ++ (offset, Ethereum.UInt256.toByteArray (words name)) :: post)
    (hbound : offset + 32 ≤ layout.size)
    (hpost : ∀ p ∈ post, offset + 32 ≤ p.1 ∨ p.1 + 32 ≤ offset)
    (hpatch : ∃ suffix, patchRuntime (ByteArray.zeroes layout.size)
      (layout.slots.map (fun slot =>
        (slot.offset, Ethereum.UInt256.toByteArray (words slot.name)))) = some suffix) :
    ((template ++ layout.suffixWords words).write (template.size + offset) mem dest 32).readWithPadding
      dest 32 = Ethereum.UInt256.toByteArray (words name) := by
  have hsize := Layout.suffixWords_size layout words
  rw [copy_window_read (template ++ layout.suffixWords words) mem
    (template.size + offset) dest 32 (by decide)
    (by rw [ByteArray.size_append, hsize]; omega)]
  rw [readWithPadding_eq_extract_unbounded _ (template.size + offset) 32 (by omega)
    (by rw [ByteArray.size_append, hsize]; omega)]
  rw [extract_append_right_window template (layout.suffixWords words) _ _ (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [show template.size + offset + 32 - template.size = offset + 32 by omega]
  rw [← readWithPadding_eq_extract (layout.suffixWords words) offset (by rw [hsize]; omega)]
  exact Layout.suffixWords_read_slot hslots hbound hpost hpatch

/-- A scalar CODECOPY has the same entire memory effect as writing its word bytes. -/
theorem Layout.codecopy_write_scalar {layout : Layout} {template mem : ByteArray}
    {words : String → Ethereum.UInt256} {name : String} {offset dest : Nat}
    {pre post : List (Nat × ByteArray)}
    (hslots : layout.slots.map (fun slot =>
      (slot.offset, Ethereum.UInt256.toByteArray (words slot.name))) =
      pre ++ (offset, Ethereum.UInt256.toByteArray (words name)) :: post)
    (hbound : offset + 32 ≤ layout.size)
    (hpost : ∀ p ∈ post, offset + 32 ≤ p.1 ∨ p.1 + 32 ≤ offset)
    (hpatch : ∃ suffix, patchRuntime (ByteArray.zeroes layout.size)
      (layout.slots.map (fun slot =>
        (slot.offset, Ethereum.UInt256.toByteArray (words slot.name)))) = some suffix) :
    (template ++ layout.suffixWords words).write (template.size + offset) mem dest 32 =
      (words name).toByteArray.write 0 mem dest 32 := by
  have hread := Layout.codecopy_read_scalar (layout := layout) (template := template)
    (mem := mem) (words := words) (name := name) (offset := offset) (dest := dest)
    hslots hbound hpost hpatch
  have hsrc : template.size + offset + 32 ≤
      (template ++ layout.suffixWords words).size := by
    rw [ByteArray.size_append, Layout.suffixWords_size]
    omega
  exact copy_word_bytes _ mem _ (template.size + offset) dest hsrc
    (by rw [toByteArray_size]) (by
      rw [← copy_window_read (template ++ layout.suffixWords words) mem
        (template.size + offset) dest 32 (by decide) hsrc]
      exact hread)

/-- MLOAD after a complete scalar CODECOPY uses the word valuation directly. -/
theorem Layout.codecopy_load_scalar {layout : Layout} {template mem : ByteArray}
    {words : String → Ethereum.UInt256} {name : String} {offset : Nat}
    {dest : Ethereum.UInt256} {pre post : List (Nat × ByteArray)}
    (hslots : layout.slots.map (fun slot =>
      (slot.offset, Ethereum.UInt256.toByteArray (words slot.name))) =
      pre ++ (offset, Ethereum.UInt256.toByteArray (words name)) :: post)
    (hbound : offset + 32 ≤ layout.size)
    (hpost : ∀ p ∈ post, offset + 32 ≤ p.1 ∨ p.1 + 32 ≤ offset)
    (hpatch : ∃ suffix, patchRuntime (ByteArray.zeroes layout.size)
      (layout.slots.map (fun slot =>
        (slot.offset, Ethereum.UInt256.toByteArray (words slot.name)))) = some suffix) :
    Reasoning.Reach.memLoad dest
      ((template ++ layout.suffixWords words).write (template.size + offset) mem dest.toNat 32) =
      words name := by
  let src := template ++ layout.suffixWords words
  have hsrc : template.size + offset + 32 ≤ src.size := by
    dsimp [src]
    rw [ByteArray.size_append, Layout.suffixWords_size]
    omega
  have hread := Layout.codecopy_read_scalar (layout := layout) (template := template)
    (mem := mem) (words := words) (name := name) (offset := offset)
    (dest := dest.toNat) hslots hbound hpost hpatch
  have hsize : dest.toNat < (src.write (template.size + offset) mem dest.toNat 32).size := by
    rw [copy_padding src mem (template.size + offset) dest.toNat 32 (by decide) hsrc]
    have hdest : dest.toNat ≤ (mem ++ ByteArray.zeroes (dest.toNat - mem.size)).size := by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega
    rw [copyWindow_size src (mem ++ ByteArray.zeroes (dest.toNat - mem.size))
      (template.size + offset) dest.toNat 32 (by decide) hsrc hdest]
    omega
  unfold Reasoning.Reach.memLoad
  rw [if_neg (by simpa [src] using Nat.not_le.mpr hsize)]
  rw [hread, Reasoning.Theory.fromByteArrayBigEndian_toByteArray,
    u256_ofNat_toNat]

/-- A `CODECOPY` of the whole immutable section leaves this slot's bytes at
    `dest + offset`. This is the Vyper counterpart of reading a patched Solidity
    `PUSH` immediate. -/
theorem Layout.codecopy_read_slot {layout : Layout} {template mem : ByteArray}
    {imms : Store} {suffix value : ByteArray} {pre post : List (Nat × ByteArray)}
    {offset dest : Nat}
    (hpatches : layout.patches? imms = some (pre ++ (offset, value) :: post))
    (hvalue : value.size = 32)
    (hbound : offset + 32 ≤ layout.size)
    (hpost : ∀ p ∈ post, offset + 32 ≤ p.1 ∨ p.1 + 32 ≤ offset)
    (hsuffix : layout.suffix? imms = some suffix) :
    ((template ++ suffix).write template.size mem dest layout.size).readWithPadding
      (dest + offset) 32 = value := by
  have hrun : patchRuntime (ByteArray.zeroes layout.size)
      (pre ++ (offset, value) :: post) = some suffix := by
    simpa [Layout.suffix?, hpatches] using hsuffix
  have hsize : suffix.size = layout.size := by
    simpa [ByteArray_zeroes_size] using patchRuntime_size_eq hrun
  rw [copy_window_read_word (template ++ suffix) mem template.size dest layout.size offset
    (by omega) (by rw [ByteArray.size_append, hsize]) hbound]
  exact Layout.runtime_read_slot hpatches hvalue hbound hpost hsuffix

#guard scalarBytes? (.fixedBytes ⟨3, by decide⟩ [0xde, 0xad, 0xbe, 0xef]) =
  some (ByteArray.mk (#[0xde, 0xad, 0xbe, 0xef] ++ Array.replicate 28 0))

#guard (Layout.suffix? { slots := [{ name := "TAG", offset := 32, length := 32 }],
                         size := 64 }
    ((∅ : Store).insert "TAG" (.fixedBytes ⟨3, by decide⟩ [0xde, 0xad, 0xbe, 0xef]))) =
  some (ByteArray.zeroes 32 ++
    ByteArray.mk (#[0xde, 0xad, 0xbe, 0xef] ++ Array.replicate 28 0))

end Reasoning.VyperImmutables
