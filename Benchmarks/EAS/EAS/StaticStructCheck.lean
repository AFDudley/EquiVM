import Benchmarks.EAS.EAS.DiffTarget
import Benchmarks.EAS.EAS.GetUIDExpr
import Benchmarks.EAS.EAS.Storage

/-!
Regression for static-mode ordering during an attestation struct write.
A malformed existing bytes header must not be decoded before the first forbidden SSTORE.
The aggregate source assignment used to revert in this case; scalar field assignments
match the bytecode's static halt. Both UID allocation sites are exercised.
-/
open Solm Solm.Interp Solm.DiffTest Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.EAS.EAS

private def bytes32 (n : Nat) : Value := .fixedBytes ⟨31,by decide⟩ (Solm.DiffTest.wordBytes n).toList

def main : IO UInt32 := do
  let t := fixtureTarget
  let caller := EVM.address 0x6004
  let payload := Solm.DiffTest.wordBytes 11
  let a : AttestationRecord := {
    uid := ⟨0⟩, schema := ⟨0⟩,time := UInt256.ofNat 1000,expirationTime := ⟨0⟩,revocationTime := ⟨0⟩,
    refUID := ⟨0⟩,recipient := caller,attester := caller,revocable := true,data := payload }
  let uid := getUIDWord a ⟨0⟩
  let slot := dbSlot uid+⟨6⟩
  IO.println s!"UID: {Ethereum.toHex uid.toByteArray}; data slot: {Ethereum.toHex slot.toByteArray}"
  let request := Value.tuple [.address caller,.int 0,.bool true,bytes32 0,.bytes payload,.int 0]
  let mut failures := 0
  for (name,args) in [("attest",[Value.tuple [bytes32 0,request]]),
      ("multiAttest",[Value.array [.tuple [bytes32 0,.array [request,request]]]])] do
    let some tr := t.contract.transitions.find? (·.name == name) | throw (IO.userError s!"no {name}")
    let selector := (Ethereum.KEC (transitionSigStr tr).toUTF8).extract 0 4
    let some input := ABI.encodeCallWithSelector? selector (tr.params.map Param.ty) args | throw (IO.userError "encoding")
    for (header,perm) in [(0,true),(0,false),(1,true),(1,false)] do
      let acc := t.world.get? t.selfAddress |>.getD default
      let accounts := t.world.insert t.selfAddress {acc with storage := acc.storage.insert slot (UInt256.ofNat header)}
      let env := t.env t.runtime caller 0 input perm 1000 16756728
      let result := runCase t {label := "static struct write",σ := accounts,I := env}
      IO.println s!"{name}, header={header}, perm={perm}: {result.verdict.describe}"
      unless result.verdict.isAgree do failures := failures+1
  if failures > 0 then return 1
  return 0
