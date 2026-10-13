import Tests.Pipeline.VyperWrapper.Bytecode
import Tests.Pipeline.VyperWrapper.Immutables

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Tests.Pipeline.VyperWrapper

/-- Runtime bytes from the constructor's immutable valuation. -/
def deployedRuntime (imms : Stele.Store) : ByteArray :=
  immutableLayout.deployed wrapperBytecode imms

/-- The compiler's slot order, with each named Stele value encoded as Vyper bytes. -/
private theorem immutablePatches (imms : Stele.Store) (v0 : Stele.Value)
    (b0 : ByteArray)
    (hget0 : imms.get? "TOKEN" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    : immutableLayout.patches? imms = some [(0, b0)] := by
  simp only [Std.HashMap.get?_eq_getElem?] at hget0
  simp [immutableLayout, Reasoning.VyperImmutables.Layout.patches?,
    Reasoning.VyperImmutables.Slot.patch?, hget0, henc0]

/-- The runtime code read for Vyper immutable `TOKEN`. -/
theorem immutableRead_TOKEN (imms : Stele.Store) (v0 : Stele.Value)
    (b0 suffix : ByteArray)
    (hget0 : imms.get? "TOKEN" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hsize : b0.size = 32)
    (hsuffix : immutableLayout.suffix? imms = some suffix)
    : (wrapperBytecode ++ suffix).readWithPadding (wrapperBytecode.size + 0) 32 = b0 := by
  apply Reasoning.VyperImmutables.Layout.runtime_read_slot
    (layout := immutableLayout) (imms := imms) (template := wrapperBytecode)
    (suffix := suffix) (value := b0) (pre := []) (post := [])
  · simpa using immutablePatches imms v0 b0 hget0 henc0
  · exact hsize
  · decide
  · simp
  · exact hsuffix

/-- Read `TOKEN` back from memory after copying the immutable section. -/
theorem immutableCopy_TOKEN (imms : Stele.Store) (v0 : Stele.Value)
    (b0 suffix mem : ByteArray) (dest : Nat)
    (hget0 : imms.get? "TOKEN" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hsize : b0.size = 32)
    (hsuffix : immutableLayout.suffix? imms = some suffix)
    : ((wrapperBytecode ++ suffix).write wrapperBytecode.size mem dest 32).readWithPadding (dest + 0) 32 = b0 := by
  apply Reasoning.VyperImmutables.Layout.codecopy_read_slot
    (layout := immutableLayout) (imms := imms) (template := wrapperBytecode)
    (suffix := suffix) (value := b0) (pre := []) (post := [])
  · simpa using immutablePatches imms v0 b0 hget0 henc0
  · exact hsize
  · decide
  · simp
  · exact hsuffix

/-- A 32-byte code copy and MLOAD of `TOKEN` returns its word. -/
theorem immutableLoad_TOKEN (immWords : String → Ethereum.UInt256)
    (mem : ByteArray) (dest : Ethereum.UInt256) :
    Reasoning.Reach.memLoad dest ((wrapperBytecode ++ immutableLayout.suffixWords immWords).write
      (wrapperBytecode.size + 0) mem dest.toNat 32) = immWords "TOKEN" := by
  have hslots :
      immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray)) =
      [] ++ (0, (immWords "TOKEN").toByteArray) :: [] := by
    rfl
  have hpatch : ∃ suffix, Stele.patchRuntime (ByteArray.zeroes immutableLayout.size)
      (immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray))) =
      some suffix := by
    simp only [immutableLayout, List.map_cons, List.map_nil]
    simp [Stele.patchRuntime, Stele.spliceBytes?, ByteArray_zeroes_size, toByteArray_size]
  have hpost : ∀ (p : Nat × ByteArray), p ∈ [] → 0 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 0 := by
    intro p hp
    simp at hp


  exact Reasoning.VyperImmutables.Layout.codecopy_load_scalar
    (layout := immutableLayout) (template := wrapperBytecode) (mem := mem)
    (words := immWords) (name := "TOKEN") (offset := 0) (dest := dest)
    (pre := []) (post := []) hslots (by decide) hpost hpatch

/-- Copying `TOKEN` from code writes its named word bytes to memory. -/
theorem immutableCopyWord_TOKEN (immWords : String → Ethereum.UInt256)
    (mem : ByteArray) (dest : Nat) :
    ((wrapperBytecode ++ immutableLayout.suffixWords immWords).write
      (wrapperBytecode.size + 0) mem dest 32) =
      (immWords "TOKEN").toByteArray.write 0 mem dest 32 := by
  have hslots :
      immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray)) =
      [] ++ (0, (immWords "TOKEN").toByteArray) :: [] := by
    rfl
  have hpatch : ∃ suffix, Stele.patchRuntime (ByteArray.zeroes immutableLayout.size)
      (immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray))) =
      some suffix := by
    simp only [immutableLayout, List.map_cons, List.map_nil]
    simp [Stele.patchRuntime, Stele.spliceBytes?, ByteArray.size_append,
      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]
  have hpost : ∀ (p : Nat × ByteArray), p ∈ [] → 0 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 0 := by
    intro p hp
    simp at hp


  exact Reasoning.VyperImmutables.Layout.codecopy_write_scalar
    (layout := immutableLayout) (template := wrapperBytecode) (mem := mem)
    (words := immWords) (name := "TOKEN") (offset := 0) (dest := dest)
    (pre := []) (post := []) hslots (by decide) hpost hpatch

/-- The scalar word valuation encodes the same suffix as the Stele store. -/
theorem immutableWordsBridge (imms : Stele.Store) (v0 : Stele.Value)
    (b0 : ByteArray)
    (hget0 : imms.get? "TOKEN" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hsize0 : b0.size = 32)
    : immutableLayout.suffixWords (Reasoning.VyperImmutables.wordsOf imms) =
      (immutableLayout.suffix? imms).getD (ByteArray.zeroes immutableLayout.size) := by
  have hp := immutablePatches imms v0 b0 hget0 henc0
  simp only [Std.HashMap.get?_eq_getElem?] at hget0
  have hw0 : Ethereum.UInt256.toByteArray
      (Reasoning.VyperImmutables.wordsOf imms "TOKEN") = b0 := by
    simp [Reasoning.VyperImmutables.wordsOf, hget0, henc0,
      Reasoning.Theory.toByteArray_uInt256OfByteArray_of_size32 hsize0]
  simp only [Reasoning.VyperImmutables.Layout.suffixWords,
    Reasoning.VyperImmutables.Layout.suffix?]
  rw [hp]
  simp [immutableLayout, hw0]

/-- The scalar word runtime agrees with the constructor's Stele valuation. -/
theorem deployedRuntime_eq_words (imms : Stele.Store) (v0 : Stele.Value)
    (b0 : ByteArray)
    (hget0 : imms.get? "TOKEN" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hsize0 : b0.size = 32)
    : deployedRuntime imms = wrapperBytecode ++
        immutableLayout.suffixWords (Reasoning.VyperImmutables.wordsOf imms) := by
  unfold deployedRuntime Reasoning.VyperImmutables.Layout.deployed
  rw [immutableWordsBridge imms v0 b0 hget0 henc0 hsize0]

/-- Constructor memory writes in slot order produce the patched runtime. -/
theorem returnedRuntime_eq_deployed (imms : Stele.Store) (returned : ByteArray)
    (v0 : Stele.Value) (b0 : ByteArray)
    (hget0 : imms.get? "TOKEN" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hsize0 : b0.size = 32)
    (hreturned : returned = wrapperBytecode ++
      Reasoning.Theory.writeCascade (ByteArray.zeroes immutableLayout.size)
        (immutableLayout.slots.map fun slot =>
          (slot.offset, Reasoning.VyperImmutables.wordsOf imms slot.name))) :
    returned = deployedRuntime imms := by
  exact Reasoning.VyperImmutables.Layout.returned_eq_deployed
    immutableLayout wrapperBytecode returned imms (by decide)
    (immutableWordsBridge imms v0 b0 hget0 henc0 hsize0) hreturned

/-- A full RETURN read of that buffer yields the patched runtime. -/
theorem returnedRuntime_read_eq_deployed (imms : Stele.Store) (returned : ByteArray)
    (v0 : Stele.Value) (b0 : ByteArray)
    (hget0 : imms.get? "TOKEN" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hsize0 : b0.size = 32)
    (hreturned : returned = wrapperBytecode ++
      Reasoning.Theory.writeCascade (ByteArray.zeroes immutableLayout.size)
        (immutableLayout.slots.map fun slot =>
          (slot.offset, Reasoning.VyperImmutables.wordsOf imms slot.name))) :
    returned.readWithPadding 0 (wrapperBytecode.size + immutableLayout.size) =
      deployedRuntime imms := by
  exact Reasoning.VyperImmutables.Layout.returned_read_eq_deployed
    immutableLayout wrapperBytecode returned imms (by decide)
    (immutableWordsBridge imms v0 b0 hget0 henc0 hsize0) hreturned (by native_decide) (by native_decide)

end Tests.Pipeline.VyperWrapper
