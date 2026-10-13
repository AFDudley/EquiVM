import Benchmarks.EAS.EAS.RecordWriteTimes
import Benchmarks.EAS.EAS.PackedAdjacent
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def recordOtherAccounts (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) (a : AttestationRecord) : AccountMap :=
  let σ1 := sstoreAccountMap ee.codeOwner σ (slot+⟨3⟩) a.refUID
  let σ2 := sstoreAccountMap ee.codeOwner σ1 (slot+⟨4⟩)
    (packedSliceWord (solcSlotWord σ1 ee (slot+⟨4⟩)) (UInt256.ofNat a.recipient.val) 0 160)
  let σ3 := sstoreAccountMap ee.codeOwner σ2 (slot+⟨5⟩)
    (packedSliceWord (solcSlotWord σ2 ee (slot+⟨5⟩)) (UInt256.ofNat a.attester.val) 0 160)
  sstoreAccountMap ee.codeOwner σ3 (slot+⟨5⟩)
    (packedSliceWord (solcSlotWord σ3 ee (slot+⟨5⟩)) a.revocable.toUInt256 160 8)

theorem recordOtherAccounts_fields (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) (a : AttestationRecord) :
    recordOtherAccounts σ ee slot a = writeScalarAccounts ((attestationScalarWrites slot a).drop 5) σ ee := by
  simp only [recordOtherAccounts,attestationScalarWrites,List.drop_succ_cons,List.drop_zero,writeScalarAccounts,
    attestationWordWrite,attestationAddressWrite,ScalarFieldWrite.accounts,bytes32Loc,addressOffset0Loc,attestationBoolLoc,
    Fin.val_zero,Fin.val_one,show (32 : Fin 33).val = 32 from rfl,show (20 : Fin 33).val = 20 from rfl,
    show (20 : Fin 32).val = 20 from rfl,Nat.mul_zero,Nat.mul_one,
    show (8 : Nat)*32 = 256 from rfl,show (8 : Nat)*20 = 160 from rfl,packedSliceWord_full]

theorem packedSliceWord_address (old : UInt256) (addr : AccountAddress) :
    packedSliceWord old (UInt256.ofNat addr.val) 0 160 =
      UInt256.lor (UInt256.ofNat addr.val) (UInt256.land (UInt256.ofNat (2^256-2^160)) old) := by
  rw [packedSliceWord_low,setLowWord]
  have hc : UInt256.land (UInt256.ofNat addr.val) (UInt256.ofNat (2^160-1)) = UInt256.ofNat addr.val :=
    addressWord_val_clean addr
  rw [hc,u256_lor_comm]

def recordOtherSingleAccounts (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) (a : AttestationRecord) : AccountMap :=
  let σ1 := sstoreAccountMap ee.codeOwner σ (slot+⟨3⟩) a.refUID
  let σ2 := sstoreAccountMap ee.codeOwner σ1 (slot+⟨4⟩)
    (UInt256.lor (UInt256.ofNat a.recipient.val) (UInt256.land (UInt256.ofNat (2^256-2^160)) (solcSlotWord σ1 ee (slot+⟨4⟩))))
  sstoreAccountMap ee.codeOwner σ2 (slot+⟨5⟩)
    (UInt256.lor (UInt256.land (UInt256.ofNat ((2^8-1)*2^160)) (UInt256.shiftLeft a.revocable.toUInt256 (UInt256.ofNat 160)))
      (UInt256.lor (UInt256.ofNat a.attester.val) (UInt256.land (solcSlotWord σ2 ee (slot+⟨5⟩)) (UInt256.ofNat (2^256-2^168)))))

theorem recordOtherAccounts_single (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) (a : AttestationRecord) :
    recordOtherAccounts σ ee slot a = recordOtherSingleAccounts σ ee slot a := by
  unfold recordOtherAccounts
  rw [sstoreAdjacentPacked _ _ _ _ _ 160 8 (by decide) (by decide),packedSliceWord_address]
  unfold recordOtherSingleAccounts adjacentPackedWord
  rw [show UInt256.land (UInt256.ofNat a.attester.val) (UInt256.ofNat (2^160-1)) = UInt256.ofNat a.attester.val from addressWord_val_clean _]
  rw [u256_land_comm (UInt256.shiftLeft a.revocable.toUInt256 (UInt256.ofNat 160))]

end Benchmarks.EAS.EAS
