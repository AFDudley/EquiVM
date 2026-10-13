import Benchmarks.Safe.ViaIR.TransactionDomainTrace
import Benchmarks.Safe.ViaIR.ByteCopy

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def transactionPrefixMemory (mem : ByteArray) (ptr : Nat) (tx : SafeTransaction) : ByteArray :=
  writeWords mem ptr ((transactionWords tx).take 9)

theorem transactionPrefixMemory_finish (mem : ByteArray) (ptr : Nat) (tx : SafeTransaction) :
    writeWord (writeWord (transactionPrefixMemory mem ptr tx) (ptr + 288)
      (UInt256.ofNat tx.refundReceiver.val)) (ptr + 320) tx.nonce =
      transactionStructMemory mem ptr tx := by
  simp only [transactionPrefixMemory, transactionStructMemory, transactionWords,
    List.take_succ_cons, List.take_zero, writeWords, Nat.add_assoc]

theorem transactionCopyHash {I : ExecutionEnv} {mem : ByteArray} {off : UInt256} {ptr : Nat}
    {payload : ByteArray} (hb : ptr < UInt256.size) (hn : payload.size < UInt256.size)
    (hp : ptr ≤ mem.size) (hi : off.toNat + payload.size ≤ I.calldata.size)
    (hd : I.calldata.extract off.toNat (off.toNat + payload.size) = payload) :
    keccakWord (UInt256.ofNat ptr) (UInt256.ofNat payload.size)
      (I.calldata.write off.toNat mem ptr payload.size) = uInt256OfByteArray (KEC payload) := by
  simp only [keccakWord, ulit_toNat' ptr hb, ulit_toNat' payload.size hn,
    copySlice_read _ _ _ _ _ hi hp, hd, uInt256OfByteArray_eq]

def transactionStructHashMemory (mem : ByteArray) (ptr : Nat) (tx : SafeTransaction) :
    ByteArray :=
  writeWord (transactionStructMemory mem ptr tx) (ptr + 64) (transactionStructWord tx)

set_option maxRecDepth 2000 in
theorem safeTransactionPrefixMemory {I : ExecutionEnv} {mem : ByteArray} {ptr : Nat}
    {off : UInt256} {tx : SafeTransaction}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 352 < UInt256.size)
    (hn : tx.payload.size < UInt256.size) (hp : ptr ≤ mem.size)
    (hi : off.toNat + tx.payload.size ≤ I.calldata.size)
    (hd : I.calldata.extract off.toNat (off.toNat + tx.payload.size) = tx.payload) :
    safeRuntime_block_9114_memory (ee := I) (mem := mem)
      (x1 := tx.operation) (x2 := tx.safeTxGas) (x3 := tx.baseGas) (x4 := tx.gasPrice)
      (x5 := UInt256.ofNat tx.gasToken.val) (x6 := UInt256.ofNat tx.refundReceiver.val)
      (x7 := tx.nonce) (x8 := tx.value) (x9 := UInt256.ofNat tx.target.val)
      (x10 := UInt256.ofNat tx.payload.size) (x11 := off) =
      transactionStructHashMemory (I.calldata.write off.toNat mem ptr tx.payload.size) ptr tx := by
  have hadd (j : Nat) (hj : j ≤ 352) :
      (UInt256.ofNat ptr + UInt256.ofNat j).toNat = ptr + j :=
    uadd_ofNat_toNat (by omega) (by omega) (by omega)
  have hs (base : ByteArray) : keccakWord (UInt256.ofNat ptr) (UInt256.ofNat 352)
      (transactionStructMemory base ptr tx) = transactionStructWord tx := by
    simp only [keccakWord, ulit_toNat' ptr (by omega),
      show (UInt256.ofNat 352).toNat = 352 by rfl, transactionStructMemory_read,
      transactionStructWord, uInt256OfByteArray_eq]
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_9114_memory, hf, ulit_toNat' ptr (by omega),
    ulit_toNat' tx.payload.size hn, hadd 32 (by decide), hadd 64 (by decide),
    hadd 96 (by decide), hadd 128 (by decide), hadd 160 (by decide), hadd 192 (by decide),
    hadd 224 (by decide), hadd 256 (by decide), hadd 288 (by decide), hadd 320 (by decide),
    transactionCopyHash (by omega) hn hp hi hd]
  change writeWord
    (transactionStructMemory (I.calldata.write off.toNat mem ptr tx.payload.size) ptr tx)
    (ptr + 64) (keccakWord (UInt256.ofNat ptr) (UInt256.ofNat 352)
      (transactionStructMemory (I.calldata.write off.toNat mem ptr tx.payload.size) ptr tx)) = _
  rw [hs]
  rfl

set_option maxRecDepth 2000 in
theorem safeTransactionFinalMemory (I : ExecutionEnv) (mem : ByteArray) (ptr : Nat)
    (tx : SafeTransaction) (hb : ptr + 352 < UInt256.size) :
    safeRuntime_block_9228_memory (mem := transactionStructHashMemory mem ptr tx)
      (x0 := UInt256.ofNat ptr) (x1 := ⟨6401⟩)
      (x2 := UInt256.ofNat ptr + UInt256.ofNat 32) (x3 := domainWord I) =
      transactionFinalMemory mem ptr I tx := by
  have hadd : (UInt256.ofNat ptr + UInt256.ofNat 32).toNat = ptr + 32 :=
    uadd_ofNat_toNat (by omega) (by decide) (by omega)
  simp only [safeRuntime_block_9228_memory, ulit_toNat' ptr (by omega), hadd]
  rfl

theorem safeTransactionFinalStack (I : ExecutionEnv) (mem : ByteArray) (ptr : Nat)
    (tx : SafeTransaction) (R : List UInt256) (hb : ptr + 352 < UInt256.size) :
    safeRuntime_block_9228_stack (mem := transactionStructHashMemory mem ptr tx)
      (x0 := UInt256.ofNat ptr) (x1 := ⟨6401⟩)
      (x2 := UInt256.ofNat ptr + UInt256.ofNat 32) (x3 := domainWord I)
      (x4 := UInt256.ofNat ptr) (x5 := ⟨30⟩) (x6 := ⟨66⟩) (R := R) =
      transactionWord I tx :: R := by
  change keccakWord (UInt256.ofNat ptr + UInt256.ofNat 30) (UInt256.ofNat 66)
    (safeRuntime_block_9228_memory (mem := transactionStructHashMemory mem ptr tx)
      (x0 := UInt256.ofNat ptr) (x1 := ⟨6401⟩)
      (x2 := UInt256.ofNat ptr + UInt256.ofNat 32) (x3 := domainWord I)) :: R = _
  rw [safeTransactionFinalMemory _ _ _ _ hb]
  have hadd : (UInt256.ofNat ptr + UInt256.ofNat 30).toNat = ptr + 30 :=
    uadd_ofNat_toNat (by omega) (by decide) (by omega)
  simp only [keccakWord, hadd, show (UInt256.ofNat 66).toNat = 66 by rfl,
    transactionFinalMemory_read, transactionWord, uInt256OfByteArray_eq]

end Benchmarks.Safe.ViaIR
