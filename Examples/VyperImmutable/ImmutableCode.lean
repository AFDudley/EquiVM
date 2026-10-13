import Examples.VyperImmutable.Bytecode
import Examples.VyperImmutable.Immutables

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Examples.VyperImmutable

/-- Runtime bytes from the constructor's immutable valuation. -/
def deployedRuntime (imms : Stele.Store) : ByteArray :=
  immutableLayout.deployed immutableBytecode imms

/-- The compiler's slot order, with each named Stele value encoded as Vyper bytes. -/
private theorem immutablePatches (imms : Stele.Store) (v0 v1 v2 : Stele.Value)
    (b0 b1 b2 : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hget1 : imms.get? "LIMIT" = some v1)
    (henc1 : Reasoning.VyperImmutables.scalarBytes? v1 = some b1)
    (hget2 : imms.get? "TAG" = some v2)
    (henc2 : Reasoning.VyperImmutables.scalarBytes? v2 = some b2)
    : immutableLayout.patches? imms = some [(0, b0), (32, b1), (64, b2)] := by
  simp only [Std.HashMap.get?_eq_getElem?] at hget0 hget1 hget2
  simp [immutableLayout, Reasoning.VyperImmutables.Layout.patches?,
    Reasoning.VyperImmutables.Slot.patch?, hget0, hget1, hget2, henc0, henc1, henc2]

/-- The runtime code read for Vyper immutable `OWNER`. -/
theorem immutableRead_OWNER (imms : Stele.Store) (v0 v1 v2 : Stele.Value)
    (b0 b1 b2 suffix : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hget1 : imms.get? "LIMIT" = some v1)
    (henc1 : Reasoning.VyperImmutables.scalarBytes? v1 = some b1)
    (hget2 : imms.get? "TAG" = some v2)
    (henc2 : Reasoning.VyperImmutables.scalarBytes? v2 = some b2)
    (hsize : b0.size = 32)
    (hsuffix : immutableLayout.suffix? imms = some suffix)
    : (immutableBytecode ++ suffix).readWithPadding (immutableBytecode.size + 0) 32 = b0 := by
  apply Reasoning.VyperImmutables.Layout.runtime_read_slot
    (layout := immutableLayout) (imms := imms) (template := immutableBytecode)
    (suffix := suffix) (value := b0) (pre := []) (post := [(32, b1), (64, b2)])
  · simpa using immutablePatches imms v0 v1 v2 b0 b1 b2 hget0 henc0 hget1 henc1 hget2 henc2
  · exact hsize
  · decide
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    all_goals omega
  · exact hsuffix

/-- Read `OWNER` back from memory after copying the immutable section. -/
theorem immutableCopy_OWNER (imms : Stele.Store) (v0 v1 v2 : Stele.Value)
    (b0 b1 b2 suffix mem : ByteArray) (dest : Nat)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hget1 : imms.get? "LIMIT" = some v1)
    (henc1 : Reasoning.VyperImmutables.scalarBytes? v1 = some b1)
    (hget2 : imms.get? "TAG" = some v2)
    (henc2 : Reasoning.VyperImmutables.scalarBytes? v2 = some b2)
    (hsize : b0.size = 32)
    (hsuffix : immutableLayout.suffix? imms = some suffix)
    : ((immutableBytecode ++ suffix).write immutableBytecode.size mem dest 96).readWithPadding (dest + 0) 32 = b0 := by
  apply Reasoning.VyperImmutables.Layout.codecopy_read_slot
    (layout := immutableLayout) (imms := imms) (template := immutableBytecode)
    (suffix := suffix) (value := b0) (pre := []) (post := [(32, b1), (64, b2)])
  · simpa using immutablePatches imms v0 v1 v2 b0 b1 b2 hget0 henc0 hget1 henc1 hget2 henc2
  · exact hsize
  · decide
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    all_goals omega
  · exact hsuffix

/-- A 32-byte code copy and MLOAD of `OWNER` returns its word. -/
theorem immutableLoad_OWNER (immWords : String → Ethereum.UInt256)
    (mem : ByteArray) (dest : Ethereum.UInt256) :
    Reasoning.Reach.memLoad dest ((immutableBytecode ++ immutableLayout.suffixWords immWords).write
      (immutableBytecode.size + 0) mem dest.toNat 32) = immWords "OWNER" := by
  have hslots :
      immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray)) =
      [] ++ (0, (immWords "OWNER").toByteArray) :: [(32, (immWords "LIMIT").toByteArray), (64, (immWords "TAG").toByteArray)] := by
    rfl
  have hpatch : ∃ suffix, Stele.patchRuntime (ByteArray.zeroes immutableLayout.size)
      (immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray))) =
      some suffix := by
    simp only [immutableLayout, List.map_cons, List.map_nil]
    simp [Stele.patchRuntime, Stele.spliceBytes?, ByteArray.size_append,
      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]
  have hpost : ∀ (p : Nat × ByteArray), p ∈ [(32, (immWords "LIMIT").toByteArray), (64, (immWords "TAG").toByteArray)] → 0 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 0 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    all_goals omega
  exact Reasoning.VyperImmutables.Layout.codecopy_load_scalar
    (layout := immutableLayout) (template := immutableBytecode) (mem := mem)
    (words := immWords) (name := "OWNER") (offset := 0) (dest := dest)
    (pre := []) (post := [(32, (immWords "LIMIT").toByteArray), (64, (immWords "TAG").toByteArray)]) hslots (by decide) hpost hpatch

/-- Copying `OWNER` from code writes its named word bytes to memory. -/
theorem immutableCopyWord_OWNER (immWords : String → Ethereum.UInt256)
    (mem : ByteArray) (dest : Nat) :
    ((immutableBytecode ++ immutableLayout.suffixWords immWords).write
      (immutableBytecode.size + 0) mem dest 32) =
      (immWords "OWNER").toByteArray.write 0 mem dest 32 := by
  have hslots :
      immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray)) =
      [] ++ (0, (immWords "OWNER").toByteArray) :: [(32, (immWords "LIMIT").toByteArray), (64, (immWords "TAG").toByteArray)] := by
    rfl
  have hpatch : ∃ suffix, Stele.patchRuntime (ByteArray.zeroes immutableLayout.size)
      (immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray))) =
      some suffix := by
    simp only [immutableLayout, List.map_cons, List.map_nil]
    simp [Stele.patchRuntime, Stele.spliceBytes?, ByteArray.size_append,
      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]
  have hpost : ∀ (p : Nat × ByteArray), p ∈ [(32, (immWords "LIMIT").toByteArray), (64, (immWords "TAG").toByteArray)] → 0 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 0 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    all_goals omega
  exact Reasoning.VyperImmutables.Layout.codecopy_write_scalar
    (layout := immutableLayout) (template := immutableBytecode) (mem := mem)
    (words := immWords) (name := "OWNER") (offset := 0) (dest := dest)
    (pre := []) (post := [(32, (immWords "LIMIT").toByteArray), (64, (immWords "TAG").toByteArray)]) hslots (by decide) hpost hpatch

/-- The runtime code read for Vyper immutable `LIMIT`. -/
theorem immutableRead_LIMIT (imms : Stele.Store) (v0 v1 v2 : Stele.Value)
    (b0 b1 b2 suffix : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hget1 : imms.get? "LIMIT" = some v1)
    (henc1 : Reasoning.VyperImmutables.scalarBytes? v1 = some b1)
    (hget2 : imms.get? "TAG" = some v2)
    (henc2 : Reasoning.VyperImmutables.scalarBytes? v2 = some b2)
    (hsize : b1.size = 32)
    (hsuffix : immutableLayout.suffix? imms = some suffix)
    : (immutableBytecode ++ suffix).readWithPadding (immutableBytecode.size + 32) 32 = b1 := by
  apply Reasoning.VyperImmutables.Layout.runtime_read_slot
    (layout := immutableLayout) (imms := imms) (template := immutableBytecode)
    (suffix := suffix) (value := b1) (pre := [(0, b0)]) (post := [(64, b2)])
  · simpa using immutablePatches imms v0 v1 v2 b0 b1 b2 hget0 henc0 hget1 henc1 hget2 henc2
  · exact hsize
  · decide
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    all_goals omega
  · exact hsuffix

/-- Read `LIMIT` back from memory after copying the immutable section. -/
theorem immutableCopy_LIMIT (imms : Stele.Store) (v0 v1 v2 : Stele.Value)
    (b0 b1 b2 suffix mem : ByteArray) (dest : Nat)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hget1 : imms.get? "LIMIT" = some v1)
    (henc1 : Reasoning.VyperImmutables.scalarBytes? v1 = some b1)
    (hget2 : imms.get? "TAG" = some v2)
    (henc2 : Reasoning.VyperImmutables.scalarBytes? v2 = some b2)
    (hsize : b1.size = 32)
    (hsuffix : immutableLayout.suffix? imms = some suffix)
    : ((immutableBytecode ++ suffix).write immutableBytecode.size mem dest 96).readWithPadding (dest + 32) 32 = b1 := by
  apply Reasoning.VyperImmutables.Layout.codecopy_read_slot
    (layout := immutableLayout) (imms := imms) (template := immutableBytecode)
    (suffix := suffix) (value := b1) (pre := [(0, b0)]) (post := [(64, b2)])
  · simpa using immutablePatches imms v0 v1 v2 b0 b1 b2 hget0 henc0 hget1 henc1 hget2 henc2
  · exact hsize
  · decide
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    all_goals omega
  · exact hsuffix

/-- A 32-byte code copy and MLOAD of `LIMIT` returns its word. -/
theorem immutableLoad_LIMIT (immWords : String → Ethereum.UInt256)
    (mem : ByteArray) (dest : Ethereum.UInt256) :
    Reasoning.Reach.memLoad dest ((immutableBytecode ++ immutableLayout.suffixWords immWords).write
      (immutableBytecode.size + 32) mem dest.toNat 32) = immWords "LIMIT" := by
  have hslots :
      immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray)) =
      [(0, (immWords "OWNER").toByteArray)] ++ (32, (immWords "LIMIT").toByteArray) :: [(64, (immWords "TAG").toByteArray)] := by
    rfl
  have hpatch : ∃ suffix, Stele.patchRuntime (ByteArray.zeroes immutableLayout.size)
      (immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray))) =
      some suffix := by
    simp only [immutableLayout, List.map_cons, List.map_nil]
    simp [Stele.patchRuntime, Stele.spliceBytes?, ByteArray.size_append,
      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]
  have hpost : ∀ (p : Nat × ByteArray), p ∈ [(64, (immWords "TAG").toByteArray)] → 32 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 32 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    all_goals omega
  exact Reasoning.VyperImmutables.Layout.codecopy_load_scalar
    (layout := immutableLayout) (template := immutableBytecode) (mem := mem)
    (words := immWords) (name := "LIMIT") (offset := 32) (dest := dest)
    (pre := [(0, (immWords "OWNER").toByteArray)]) (post := [(64, (immWords "TAG").toByteArray)]) hslots (by decide) hpost hpatch

/-- Copying `LIMIT` from code writes its named word bytes to memory. -/
theorem immutableCopyWord_LIMIT (immWords : String → Ethereum.UInt256)
    (mem : ByteArray) (dest : Nat) :
    ((immutableBytecode ++ immutableLayout.suffixWords immWords).write
      (immutableBytecode.size + 32) mem dest 32) =
      (immWords "LIMIT").toByteArray.write 0 mem dest 32 := by
  have hslots :
      immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray)) =
      [(0, (immWords "OWNER").toByteArray)] ++ (32, (immWords "LIMIT").toByteArray) :: [(64, (immWords "TAG").toByteArray)] := by
    rfl
  have hpatch : ∃ suffix, Stele.patchRuntime (ByteArray.zeroes immutableLayout.size)
      (immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray))) =
      some suffix := by
    simp only [immutableLayout, List.map_cons, List.map_nil]
    simp [Stele.patchRuntime, Stele.spliceBytes?, ByteArray.size_append,
      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]
  have hpost : ∀ (p : Nat × ByteArray), p ∈ [(64, (immWords "TAG").toByteArray)] → 32 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 32 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    all_goals omega
  exact Reasoning.VyperImmutables.Layout.codecopy_write_scalar
    (layout := immutableLayout) (template := immutableBytecode) (mem := mem)
    (words := immWords) (name := "LIMIT") (offset := 32) (dest := dest)
    (pre := [(0, (immWords "OWNER").toByteArray)]) (post := [(64, (immWords "TAG").toByteArray)]) hslots (by decide) hpost hpatch

/-- The runtime code read for Vyper immutable `TAG`. -/
theorem immutableRead_TAG (imms : Stele.Store) (v0 v1 v2 : Stele.Value)
    (b0 b1 b2 suffix : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hget1 : imms.get? "LIMIT" = some v1)
    (henc1 : Reasoning.VyperImmutables.scalarBytes? v1 = some b1)
    (hget2 : imms.get? "TAG" = some v2)
    (henc2 : Reasoning.VyperImmutables.scalarBytes? v2 = some b2)
    (hsize : b2.size = 32)
    (hsuffix : immutableLayout.suffix? imms = some suffix)
    : (immutableBytecode ++ suffix).readWithPadding (immutableBytecode.size + 64) 32 = b2 := by
  apply Reasoning.VyperImmutables.Layout.runtime_read_slot
    (layout := immutableLayout) (imms := imms) (template := immutableBytecode)
    (suffix := suffix) (value := b2) (pre := [(0, b0), (32, b1)]) (post := [])
  · simpa using immutablePatches imms v0 v1 v2 b0 b1 b2 hget0 henc0 hget1 henc1 hget2 henc2
  · exact hsize
  · decide
  · simp
  · exact hsuffix

/-- Read `TAG` back from memory after copying the immutable section. -/
theorem immutableCopy_TAG (imms : Stele.Store) (v0 v1 v2 : Stele.Value)
    (b0 b1 b2 suffix mem : ByteArray) (dest : Nat)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hget1 : imms.get? "LIMIT" = some v1)
    (henc1 : Reasoning.VyperImmutables.scalarBytes? v1 = some b1)
    (hget2 : imms.get? "TAG" = some v2)
    (henc2 : Reasoning.VyperImmutables.scalarBytes? v2 = some b2)
    (hsize : b2.size = 32)
    (hsuffix : immutableLayout.suffix? imms = some suffix)
    : ((immutableBytecode ++ suffix).write immutableBytecode.size mem dest 96).readWithPadding (dest + 64) 32 = b2 := by
  apply Reasoning.VyperImmutables.Layout.codecopy_read_slot
    (layout := immutableLayout) (imms := imms) (template := immutableBytecode)
    (suffix := suffix) (value := b2) (pre := [(0, b0), (32, b1)]) (post := [])
  · simpa using immutablePatches imms v0 v1 v2 b0 b1 b2 hget0 henc0 hget1 henc1 hget2 henc2
  · exact hsize
  · decide
  · simp
  · exact hsuffix

/-- A 32-byte code copy and MLOAD of `TAG` returns its word. -/
theorem immutableLoad_TAG (immWords : String → Ethereum.UInt256)
    (mem : ByteArray) (dest : Ethereum.UInt256) :
    Reasoning.Reach.memLoad dest ((immutableBytecode ++ immutableLayout.suffixWords immWords).write
      (immutableBytecode.size + 64) mem dest.toNat 32) = immWords "TAG" := by
  have hslots :
      immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray)) =
      [(0, (immWords "OWNER").toByteArray), (32, (immWords "LIMIT").toByteArray)] ++ (64, (immWords "TAG").toByteArray) :: [] := by
    rfl
  have hpatch : ∃ suffix, Stele.patchRuntime (ByteArray.zeroes immutableLayout.size)
      (immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray))) =
      some suffix := by
    simp only [immutableLayout, List.map_cons, List.map_nil]
    simp [Stele.patchRuntime, Stele.spliceBytes?, ByteArray.size_append,
      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]
  have hpost : ∀ (p : Nat × ByteArray), p ∈ [] → 64 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 64 := by
    intro p hp
    simp at hp


  exact Reasoning.VyperImmutables.Layout.codecopy_load_scalar
    (layout := immutableLayout) (template := immutableBytecode) (mem := mem)
    (words := immWords) (name := "TAG") (offset := 64) (dest := dest)
    (pre := [(0, (immWords "OWNER").toByteArray), (32, (immWords "LIMIT").toByteArray)]) (post := []) hslots (by decide) hpost hpatch

/-- Copying `TAG` from code writes its named word bytes to memory. -/
theorem immutableCopyWord_TAG (immWords : String → Ethereum.UInt256)
    (mem : ByteArray) (dest : Nat) :
    ((immutableBytecode ++ immutableLayout.suffixWords immWords).write
      (immutableBytecode.size + 64) mem dest 32) =
      (immWords "TAG").toByteArray.write 0 mem dest 32 := by
  have hslots :
      immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray)) =
      [(0, (immWords "OWNER").toByteArray), (32, (immWords "LIMIT").toByteArray)] ++ (64, (immWords "TAG").toByteArray) :: [] := by
    rfl
  have hpatch : ∃ suffix, Stele.patchRuntime (ByteArray.zeroes immutableLayout.size)
      (immutableLayout.slots.map (fun slot => (slot.offset, (immWords slot.name).toByteArray))) =
      some suffix := by
    simp only [immutableLayout, List.map_cons, List.map_nil]
    simp [Stele.patchRuntime, Stele.spliceBytes?, ByteArray.size_append,
      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]
  have hpost : ∀ (p : Nat × ByteArray), p ∈ [] → 64 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 64 := by
    intro p hp
    simp at hp


  exact Reasoning.VyperImmutables.Layout.codecopy_write_scalar
    (layout := immutableLayout) (template := immutableBytecode) (mem := mem)
    (words := immWords) (name := "TAG") (offset := 64) (dest := dest)
    (pre := [(0, (immWords "OWNER").toByteArray), (32, (immWords "LIMIT").toByteArray)]) (post := []) hslots (by decide) hpost hpatch

/-- The scalar word valuation encodes the same suffix as the Stele store. -/
theorem immutableWordsBridge (imms : Stele.Store) (v0 v1 v2 : Stele.Value)
    (b0 b1 b2 : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hget1 : imms.get? "LIMIT" = some v1)
    (henc1 : Reasoning.VyperImmutables.scalarBytes? v1 = some b1)
    (hget2 : imms.get? "TAG" = some v2)
    (henc2 : Reasoning.VyperImmutables.scalarBytes? v2 = some b2)
    (hsize0 : b0.size = 32) (hsize1 : b1.size = 32) (hsize2 : b2.size = 32)
    : immutableLayout.suffixWords (Reasoning.VyperImmutables.wordsOf imms) =
      (immutableLayout.suffix? imms).getD (ByteArray.zeroes immutableLayout.size) := by
  have hp := immutablePatches imms v0 v1 v2 b0 b1 b2 hget0 henc0 hget1 henc1 hget2 henc2
  simp only [Std.HashMap.get?_eq_getElem?] at hget0 hget1 hget2
  have hw0 : Ethereum.UInt256.toByteArray
      (Reasoning.VyperImmutables.wordsOf imms "OWNER") = b0 := by
    simp [Reasoning.VyperImmutables.wordsOf, hget0, henc0,
      Reasoning.Theory.toByteArray_uInt256OfByteArray_of_size32 hsize0]
  have hw1 : Ethereum.UInt256.toByteArray
      (Reasoning.VyperImmutables.wordsOf imms "LIMIT") = b1 := by
    simp [Reasoning.VyperImmutables.wordsOf, hget1, henc1,
      Reasoning.Theory.toByteArray_uInt256OfByteArray_of_size32 hsize1]
  have hw2 : Ethereum.UInt256.toByteArray
      (Reasoning.VyperImmutables.wordsOf imms "TAG") = b2 := by
    simp [Reasoning.VyperImmutables.wordsOf, hget2, henc2,
      Reasoning.Theory.toByteArray_uInt256OfByteArray_of_size32 hsize2]
  simp only [Reasoning.VyperImmutables.Layout.suffixWords,
    Reasoning.VyperImmutables.Layout.suffix?]
  rw [hp]
  simp [immutableLayout, hw0, hw1, hw2]

/-- The scalar word runtime agrees with the constructor's Stele valuation. -/
theorem deployedRuntime_eq_words (imms : Stele.Store) (v0 v1 v2 : Stele.Value)
    (b0 b1 b2 : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hget1 : imms.get? "LIMIT" = some v1)
    (henc1 : Reasoning.VyperImmutables.scalarBytes? v1 = some b1)
    (hget2 : imms.get? "TAG" = some v2)
    (henc2 : Reasoning.VyperImmutables.scalarBytes? v2 = some b2)
    (hsize0 : b0.size = 32) (hsize1 : b1.size = 32) (hsize2 : b2.size = 32)
    : deployedRuntime imms = immutableBytecode ++
        immutableLayout.suffixWords (Reasoning.VyperImmutables.wordsOf imms) := by
  unfold deployedRuntime Reasoning.VyperImmutables.Layout.deployed
  rw [immutableWordsBridge imms v0 v1 v2 b0 b1 b2 hget0 henc0 hget1 henc1 hget2 henc2 hsize0 hsize1 hsize2]

/-- Constructor memory writes in slot order produce the patched runtime. -/
theorem returnedRuntime_eq_deployed (imms : Stele.Store) (returned : ByteArray)
    (v0 v1 v2 : Stele.Value) (b0 b1 b2 : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hget1 : imms.get? "LIMIT" = some v1)
    (henc1 : Reasoning.VyperImmutables.scalarBytes? v1 = some b1)
    (hget2 : imms.get? "TAG" = some v2)
    (henc2 : Reasoning.VyperImmutables.scalarBytes? v2 = some b2)
    (hsize0 : b0.size = 32) (hsize1 : b1.size = 32) (hsize2 : b2.size = 32)
    (hreturned : returned = immutableBytecode ++
      Reasoning.Theory.writeCascade (ByteArray.zeroes immutableLayout.size)
        (immutableLayout.slots.map fun slot =>
          (slot.offset, Reasoning.VyperImmutables.wordsOf imms slot.name))) :
    returned = deployedRuntime imms := by
  exact Reasoning.VyperImmutables.Layout.returned_eq_deployed
    immutableLayout immutableBytecode returned imms (by decide)
    (immutableWordsBridge imms v0 v1 v2 b0 b1 b2 hget0 henc0 hget1 henc1 hget2 henc2 hsize0 hsize1 hsize2) hreturned

/-- A full RETURN read of that buffer yields the patched runtime. -/
theorem returnedRuntime_read_eq_deployed (imms : Stele.Store) (returned : ByteArray)
    (v0 v1 v2 : Stele.Value) (b0 b1 b2 : ByteArray)
    (hget0 : imms.get? "OWNER" = some v0)
    (henc0 : Reasoning.VyperImmutables.scalarBytes? v0 = some b0)
    (hget1 : imms.get? "LIMIT" = some v1)
    (henc1 : Reasoning.VyperImmutables.scalarBytes? v1 = some b1)
    (hget2 : imms.get? "TAG" = some v2)
    (henc2 : Reasoning.VyperImmutables.scalarBytes? v2 = some b2)
    (hsize0 : b0.size = 32) (hsize1 : b1.size = 32) (hsize2 : b2.size = 32)
    (hreturned : returned = immutableBytecode ++
      Reasoning.Theory.writeCascade (ByteArray.zeroes immutableLayout.size)
        (immutableLayout.slots.map fun slot =>
          (slot.offset, Reasoning.VyperImmutables.wordsOf imms slot.name))) :
    returned.readWithPadding 0 (immutableBytecode.size + immutableLayout.size) =
      deployedRuntime imms := by
  exact Reasoning.VyperImmutables.Layout.returned_read_eq_deployed
    immutableLayout immutableBytecode returned imms (by decide)
    (immutableWordsBridge imms v0 v1 v2 b0 b1 b2 hget0 henc0 hget1 henc1 hget2 henc2 hsize0 hsize1 hsize2) hreturned (by native_decide) (by native_decide)

end Examples.VyperImmutable
