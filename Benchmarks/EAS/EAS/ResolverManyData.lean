import Benchmarks.EAS.EAS.ArraysEncode
import Benchmarks.EAS.EAS.ArrayFrameViews
import Benchmarks.EAS.EAS.ResolverManySource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolverManySelectorWord (rev : Bool) : UInt256 :=
  if rev then UInt256.ofNat 0x88e5b2d900000000000000000000000000000000000000000000000000000000
  else UInt256.ofNat 0x91db0b7e00000000000000000000000000000000000000000000000000000000

theorem resolverManySelectorWord_bytes (rev : Bool) :
    (resolverManySelectorWord rev).toByteArray.extract 0 4 = (resolverManySelector rev).toByteArray := by
  cases rev <;> decide +kernel

theorem resolverManySelector_size (rev : Bool) : (resolverManySelector rev).toByteArray.size = 4 := by
  rw [list_toByteArray_size]
  cases rev <;> rfl

theorem resolverManyPayload_size (ats : List AttestationRecord) (values : List UInt256) (rev : Bool) :
    (resolverManyPayload ats values rev).size = 4+(resolverArraysBody ats values).size := by
  change ((resolverManySelector rev).toByteArray ++ resolverArraysBody ats values).size = _
  rw [ByteArray.size_append, resolverManySelector_size]

def resolverManyHeaderMemory (mem : ByteArray) (ptr : UInt256) (rev : Bool) : ByteArray :=
  Reasoning.Theory.writeWord mem ptr.toNat (resolverManySelectorWord rev)

theorem resolverManyHeaderMemory_prefix (mem : ByteArray) (ptr : UInt256) (rev : Bool) :
    MemoryPrefix mem (resolverManyHeaderMemory mem ptr rev) ptr.toNat :=
  memoryPrefix_sparse_writeWord mem ptr.toNat ptr.toNat _ (Or.inl (le_refl _))

theorem resolverManyHeaderMemory_selector (mem : ByteArray) (ptr : UInt256) (rev : Bool) :
    (resolverManyHeaderMemory mem ptr rev).readWithPadding ptr.toNat 4 = (resolverManySelector rev).toByteArray := by
  rw [← readWithPadding_prefix _ ptr.toNat 32 4 (by decide)
    (by simp only [resolverManyHeaderMemory, writeWord_sparse_size]; omega),
    show resolverManyHeaderMemory mem ptr rev = Reasoning.Theory.writeWord mem ptr.toNat (resolverManySelectorWord rev) from rfl,
    writeWord_sparse_read_back, resolverManySelectorWord_bytes]

theorem resolverManyEncoded_read {mem after : ByteArray} {ptr : UInt256} {rev : Bool}
    {ats : List AttestationRecord} {values : List UInt256}
    (hlo : 124 ≤ ptr.toNat)
    (hp : MemoryPrefix (resolverManyHeaderMemory mem ptr rev) after (ptr.toNat+4))
    (hr : after.readWithPadding (ptr.toNat+4) (resolverArraysBody ats values).size = resolverArraysBody ats values)
    (hc : ptr.toNat+4+(resolverArraysBody ats values).size ≤ after.size) :
    after.readWithPadding ptr.toNat (resolverManyPayload ats values rev).size = resolverManyPayload ats values rev := by
  have hs : after.readWithPadding ptr.toNat 4 = (resolverManySelector rev).toByteArray := by
    rw [memoryPrefix_read_suffix hp ptr.toNat 4 (by decide) (by omega) (le_refl _)
      (by simp only [resolverManyHeaderMemory, writeWord_sparse_size]; omega), resolverManyHeaderMemory_selector]
  have h := readWithPadding_concat after ptr.toNat (resolverManySelector rev).toByteArray (resolverArraysBody ats values)
    (by rw [resolverManySelector_size]; exact hs)
    (by rw [resolverManySelector_size]; exact hr)
    (by rw [resolverManySelector_size]; exact hc)
  simpa only [resolverManyPayload, resolverArraysBody, ByteArray.size_append] using h

end Benchmarks.EAS.EAS
