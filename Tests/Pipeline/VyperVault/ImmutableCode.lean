import Tests.Pipeline.VyperVault.Bytecode
import Tests.Pipeline.VyperVault.Immutables

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Tests.Pipeline.VyperVault

/-- Runtime bytes from the constructor's immutable valuation. -/
def deployedRuntime (imms : Solm.Store) : ByteArray :=
  immutableLayout.deployed vyperVaultBytecode imms

/-- The compiler's slot order, with each named Solm value encoded as Vyper bytes. -/
private theorem immutablePatches (imms : Solm.Store) (v0 : Solm.Value)
    (b0 : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    : immutableLayout.patches? imms = some [(0, b0)] := by
  simp only [Std.HashMap.get?_eq_getElem?] at hget0
  simp [immutableLayout, Reasoning.VyperImmutables.Layout.patches?,
    Reasoning.VyperImmutables.Slot.patch?, hget0, henc0]

/-- The runtime code read for Vyper immutable `OWNER`. -/
theorem immutableRead_OWNER (imms : Solm.Store) (v0 : Solm.Value)
    (b0 suffix : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hsize : b0.size = 32)
    (hsuffix : immutableLayout.suffix? imms = some suffix)
    : (vyperVaultBytecode ++ suffix).readWithPadding (vyperVaultBytecode.size + 0) 32 = b0 := by
  apply Reasoning.VyperImmutables.Layout.runtime_read_slot
    (layout := immutableLayout) (imms := imms) (template := vyperVaultBytecode)
    (suffix := suffix) (value := b0) (pre := []) (post := [])
  · simpa using immutablePatches imms v0 b0 hget0 henc0
  · exact hsize
  · decide
  · simp
  · exact hsuffix

/-- Read `OWNER` back from memory after copying the immutable section. -/
theorem immutableCopy_OWNER (imms : Solm.Store) (v0 : Solm.Value)
    (b0 suffix mem : ByteArray) (dest : Nat)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hsize : b0.size = 32)
    (hsuffix : immutableLayout.suffix? imms = some suffix)
    : ((vyperVaultBytecode ++ suffix).write vyperVaultBytecode.size mem dest 32).readWithPadding (dest + 0) 32 = b0 := by
  apply Reasoning.VyperImmutables.Layout.codecopy_read_slot
    (layout := immutableLayout) (imms := imms) (template := vyperVaultBytecode)
    (suffix := suffix) (value := b0) (pre := []) (post := [])
  · simpa using immutablePatches imms v0 b0 hget0 henc0
  · exact hsize
  · decide
  · simp
  · exact hsuffix

/-- A 32-byte code copy and MLOAD of `OWNER` returns its word. -/
theorem immutableLoad_OWNER (immWords : String → Ethereum.UInt256)
    (mem : ByteArray) (dest : Ethereum.UInt256) :
    Reasoning.Reach.memLoad dest ((vyperVaultBytecode ++ immutableLayout.suffixWords immWords).write
      (vyperVaultBytecode.size + 0) mem dest.toNat 32) = immWords "OWNER" := by
  have hslots :
      immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray)) =
      [] ++ (0, (immWords "OWNER").toByteArray) :: [] := by
    rfl
  have hpatch : ∃ suffix, Solm.patchRuntime (ByteArray.zeroes immutableLayout.size)
      (immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray))) =
      some suffix := by
    simp only [immutableLayout, List.map_cons, List.map_nil]
    simp [Solm.patchRuntime, Solm.spliceBytes?, ByteArray.size_append,
      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]
  have hpost : ∀ (p : Nat × ByteArray), p ∈ [] → 0 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 0 := by
    intro p hp
    simp at hp


  exact Reasoning.VyperImmutables.Layout.codecopy_load_scalar
    (layout := immutableLayout) (template := vyperVaultBytecode) (mem := mem)
    (words := immWords) (name := "OWNER") (offset := 0) (dest := dest)
    (pre := []) (post := []) hslots (by decide) hpost hpatch

/-- Copying `OWNER` from code writes its named word bytes to memory. -/
theorem immutableCopyWord_OWNER (immWords : String → Ethereum.UInt256)
    (mem : ByteArray) (dest : Nat) :
    ((vyperVaultBytecode ++ immutableLayout.suffixWords immWords).write
      (vyperVaultBytecode.size + 0) mem dest 32) =
      (immWords "OWNER").toByteArray.write 0 mem dest 32 := by
  have hslots :
      immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray)) =
      [] ++ (0, (immWords "OWNER").toByteArray) :: [] := by
    rfl
  have hpatch : ∃ suffix, Solm.patchRuntime (ByteArray.zeroes immutableLayout.size)
      (immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray))) =
      some suffix := by
    simp only [immutableLayout, List.map_cons, List.map_nil]
    simp [Solm.patchRuntime, Solm.spliceBytes?, ByteArray.size_append,
      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]
  have hpost : ∀ (p : Nat × ByteArray), p ∈ [] → 0 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 0 := by
    intro p hp
    simp at hp


  exact Reasoning.VyperImmutables.Layout.codecopy_write_scalar
    (layout := immutableLayout) (template := vyperVaultBytecode) (mem := mem)
    (words := immWords) (name := "OWNER") (offset := 0) (dest := dest)
    (pre := []) (post := []) hslots (by decide) hpost hpatch

/-- The scalar word valuation encodes the same suffix as the Solm store. -/
theorem immutableWordsBridge (imms : Solm.Store) (v0 : Solm.Value)
    (b0 : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hsize0 : b0.size = 32)
    : immutableLayout.suffixWords (Reasoning.VyperImmutables.wordsOf imms) =
      (immutableLayout.suffix? imms).getD (ByteArray.zeroes immutableLayout.size) := by
  have hp := immutablePatches imms v0 b0 hget0 henc0
  simp only [Std.HashMap.get?_eq_getElem?] at hget0
  have hw0 : Ethereum.UInt256.toByteArray
      (Reasoning.VyperImmutables.wordsOf imms "OWNER") = b0 := by
    simp [Reasoning.VyperImmutables.wordsOf, hget0, henc0,
      Reasoning.Theory.toByteArray_uInt256OfByteArray_of_size32 hsize0]
  simp only [Reasoning.VyperImmutables.Layout.suffixWords,
    Reasoning.VyperImmutables.Layout.suffix?]
  rw [hp]
  simp [immutableLayout, hw0]

/-- The scalar word runtime agrees with the constructor's Solm valuation. -/
theorem deployedRuntime_eq_words (imms : Solm.Store) (v0 : Solm.Value)
    (b0 : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hsize0 : b0.size = 32)
    : deployedRuntime imms = vyperVaultBytecode ++
        immutableLayout.suffixWords (Reasoning.VyperImmutables.wordsOf imms) := by
  unfold deployedRuntime Reasoning.VyperImmutables.Layout.deployed
  rw [immutableWordsBridge imms v0 b0 hget0 henc0 hsize0]

/-- Constructor memory writes in slot order produce the patched runtime. -/
theorem returnedRuntime_eq_deployed (imms : Solm.Store) (returned : ByteArray)
    (v0 : Solm.Value) (b0 : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hsize0 : b0.size = 32)
    (hreturned : returned = vyperVaultBytecode ++
      Reasoning.Theory.writeCascade (ByteArray.zeroes immutableLayout.size)
        (immutableLayout.slots.map fun slot =>
          (slot.offset, Reasoning.VyperImmutables.wordsOf imms slot.name))) :
    returned = deployedRuntime imms := by
  exact Reasoning.VyperImmutables.Layout.returned_eq_deployed
    immutableLayout vyperVaultBytecode returned imms (by decide)
    (immutableWordsBridge imms v0 b0 hget0 henc0 hsize0) hreturned

/-- A full RETURN read of that buffer yields the patched runtime. -/
theorem returnedRuntime_read_eq_deployed (imms : Solm.Store) (returned : ByteArray)
    (v0 : Solm.Value) (b0 : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hsize0 : b0.size = 32)
    (hreturned : returned = vyperVaultBytecode ++
      Reasoning.Theory.writeCascade (ByteArray.zeroes immutableLayout.size)
        (immutableLayout.slots.map fun slot =>
          (slot.offset, Reasoning.VyperImmutables.wordsOf imms slot.name))) :
    returned.readWithPadding 0 (vyperVaultBytecode.size + immutableLayout.size) =
      deployedRuntime imms := by
  exact Reasoning.VyperImmutables.Layout.returned_read_eq_deployed
    immutableLayout vyperVaultBytecode returned imms (by decide)
    (immutableWordsBridge imms v0 b0 hget0 henc0 hsize0) hreturned (by native_decide) (by native_decide)

end Tests.Pipeline.VyperVault
