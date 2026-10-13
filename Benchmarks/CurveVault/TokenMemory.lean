import Benchmarks.CurveVault.Calls
import Benchmarks.CurveVault.Memory

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

def vaultTokenPayload (sender recipient amount : UInt256) : ByteArray :=
  selectorBytes 0x23 0xb8 0x72 0xdd ++ ((sender.toByteArray ++ recipient.toByteArray) ++ amount.toByteArray)

theorem vaultTokenPayload_size (sender recipient amount : UInt256) :
    (vaultTokenPayload sender recipient amount).size = 100 := by
  simp only [vaultTokenPayload, ByteArray.size_append, toByteArray_size]
  rfl

theorem vaultTokenPayload_encode (sender recipient amount : UInt256) :
    config.externalABI.encode? "transferFrom"
      [.int (Int.ofNat sender.toNat), .int (Int.ofNat recipient.toNat), .int (Int.ofNat amount.toNat)] =
      some (vaultTokenPayload sender recipient amount) := by
  change ABI.encodeCallWithSelector? (selectorBytes 0x23 0xb8 0x72 0xdd)
    [abiUInt256, abiUInt256, abiUInt256] _ = _
  rw [ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    show abiTupleHeadSize? [abiUInt256, abiUInt256, abiUInt256] = some 96 from by native_decide]
  simp only [bind, Option.bind, encodeABIValuesFrom?, encodeABIValue_uint256_word,
    show isDynamicABIType abiUInt256 = false from rfl, Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil]
  apply congrArg some
  apply congrArg (fun bytes => selectorBytes 0x23 0xb8 0x72 0xdd ++ bytes)
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_append, Array.toList_append, List.toList_data_toByteArray,
    byteArray_toList_eq]

def vaultTokenSelectorMemory (mem : ByteArray) : ByteArray :=
  (UInt256.ofNat 599290589).toByteArray.write 0 mem 192 32

def vaultTokenCallMemory (mem : ByteArray) : ByteArray :=
  (vaultTokenSelectorMemory mem).write 96 (vaultTokenSelectorMemory mem) 224 96

theorem vaultTokenSelectorMemory_size (mem : ByteArray) :
    (vaultTokenSelectorMemory mem).size = max mem.size 224 :=
  writeWord_size mem 192 (UInt256.ofNat 599290589)
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by omega)))

theorem vaultTokenCallMemory_size (mem : ByteArray) :
    (vaultTokenCallMemory mem).size = max mem.size 320 := by
  have hsize := vaultTokenSelectorMemory_size mem
  rw [vaultTokenCallMemory, copyWindow_size _ _ _ _ _ (by omega) (by omega) (by omega), hsize]
  omega

theorem vaultTokenCallMemory_frame (mem : ByteArray) :
    WordMemoryRange mem (vaultTokenCallMemory mem) 320 UInt256.size := by
  have hsize := vaultTokenSelectorMemory_size mem
  exact (wordMemoryRange_write mem (UInt256.ofNat 599290589) 192 320 UInt256.size
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by omega))) (Or.inr (by omega))).trans
    (wordMemoryRange_copy (vaultTokenSelectorMemory mem) (vaultTokenSelectorMemory mem)
      96 224 96 320 UInt256.size (by omega) (by omega) (by omega) (Or.inr (by omega)))

-- LIBRARY CANDIDATE: an in-bounds word read is determined by memLoad.
theorem readWithPadding_of_memLoad (mem : ByteArray) (off : Nat) (word : UInt256)
    (hin : off + 32 ≤ mem.size) (hoff : off < UInt256.size)
    (hload : memLoad (UInt256.ofNat off) mem = word) :
    mem.readWithPadding off 32 = word.toByteArray := by
  unfold memLoad at hload
  rw [ulit_toNat' _ hoff, if_neg (by omega), readWithPadding_eq_extract _ _ hin] at hload
  rw [readWithPadding_eq_toByteArray_ofNat _ _ hin, hload]

-- LIBRARY CANDIDATE: arbitrary short reads below a memory copy are preserved.
theorem copyWindow_read_below_len (src mem : ByteArray) (srcOff dest len off count : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hcount : 0 < count) (hbelow : off + count ≤ dest) :
    (src.write srcOff mem dest len).readWithPadding off count = mem.readWithPadding off count := by
  have hsize := copyWindow_size src mem srcOff dest len hpos hsrc hdest
  have hp : (mem.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  have hc : (src.extract srcOff (srcOff + len)).size = len := by rw [ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract_unbounded _ _ _ hcount (by omega),
    readWithPadding_eq_extract_unbounded _ _ _ hcount (by omega),
    copyWindow_eq src mem srcOff dest len hpos hsrc hdest,
    extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hp, hc]; omega),
    extract_append_left _ _ _ _ (by rw [hp]; omega), extract_prefix _ _ _ _ (by omega)]

theorem vaultTokenCallMemory_payload (mem : ByteArray) (sender recipient amount : UInt256)
    (hsize : 192 ≤ mem.size)
    (hfrom : memLoad (UInt256.ofNat 96) mem = sender)
    (hto : memLoad (UInt256.ofNat 128) mem = recipient)
    (hamount : memLoad (UInt256.ofNat 160) mem = amount) :
    (vaultTokenCallMemory mem).readWithPadding 220 100 = vaultTokenPayload sender recipient amount := by
  have hm := vaultTokenSelectorMemory_size mem
  have hc := vaultTokenCallMemory_size mem
  have hgap : 192 - mem.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by omega))
  have hselector : (vaultTokenCallMemory mem).readWithPadding 220 4 = selectorBytes 0x23 0xb8 0x72 0xdd := by
    rw [vaultTokenCallMemory, copyWindow_read_below_len _ _ 96 224 96 220 4
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    change ((UInt256.ofNat 599290589).toByteArray.write 0 mem 192 32).readWithPadding (192 + 28) 4 = _
    rw [toByteArray_write_read_window_of_gap _ _ _ 28 4 (by omega) (by omega) (by omega) hgap]
    native_decide
  have hword (off : Nat) (hoff : off + 32 ≤ 96) :
      (vaultTokenCallMemory mem).readWithPadding (224 + off) 32 = mem.readWithPadding (96 + off) 32 := by
    rw [vaultTokenCallMemory, copyWindow_read_word _ _ 96 224 96 off (by omega) (by omega) (by omega) hoff]
    exact toByteArray_write_read_below_of_gap _ mem 192 (96 + off) (by omega) (by omega) hgap
  rw [byteArray_readWithPadding_split_unbounded _ 220 4 96 (by omega) (by omega) (by omega)]
  change _ ++ (vaultTokenCallMemory mem).readWithPadding 224 (32 + 64) = _
  rw [byteArray_readWithPadding_split_unbounded _ 224 32 64 (by omega) (by omega) (by omega)]
  change _ ++ (_ ++ (vaultTokenCallMemory mem).readWithPadding 256 (32 + 32)) = _
  rw [byteArray_readWithPadding_split_unbounded _ 256 32 32 (by omega) (by omega) (by omega),
    hselector, hword 0 (by omega), hword 32 (by omega), hword 64 (by omega)]
  rw [readWithPadding_of_memLoad mem 96 sender (by omega) (by decide +kernel) hfrom,
    readWithPadding_of_memLoad mem 128 recipient (by omega) (by decide +kernel) hto,
    readWithPadding_of_memLoad mem 160 amount hsize (by decide +kernel) hamount]
  exact congrArg (fun bytes => selectorBytes 0x23 0xb8 0x72 0xdd ++ bytes) ByteArray.append_assoc.symm

end Benchmarks.CurveVault
