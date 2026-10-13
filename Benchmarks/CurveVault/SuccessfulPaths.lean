import Benchmarks.CurveVault.DiffTarget

open Stele Stele.DiffTest Stele.Interp ABI Ethereum Ethereum.EVM
open Benchmarks.CurveVault

namespace Benchmarks.CurveVault.SuccessfulPaths

def addr (n : Nat) : Value := .address (EVM.address n)

def seeded : AccountMap := Id.run do
  let t := diffTarget
  let I := t.env t.runtime (EVM.address 0x2000) 0 .empty true
  let mut evm := initialState t.world t.world (UInt256.ofNat t.gas) default I
  for (slot, value) in [(0, 0x6001), (1, 0x6001), (2, 0x6000), (3, 0x6000),
      (4, 0x6000), (5, 2^256-1), (14, 100000), (15, 1)] do
    evm := EVM.storageStore evm t.selfAddress (UInt256.ofNat slot) (UInt256.ofNat value)
  let balanceSlot := vyperMappingSlot (UInt256.ofNat 13) (.address (EVM.address 0x2000))
  evm := EVM.storageStore evm t.selfAddress balanceSlot (UInt256.ofNat 100000)
  let allowanceSlot := vyperMappingSlot
    (vyperMappingSlot (UInt256.ofNat 12) (.address (EVM.address 0x2000)))
    (.address (EVM.address 0x2000))
  evm := EVM.storageStore evm t.selfAddress allowanceSlot (UInt256.ofNat (2^256-1))
  return evm.accountMap

def argument (p : Param) : Value :=
  match p.ty with
  | .elem .address => addr (if p.name == "_owner" || p.name == "_from" then 0x2000 else 0x3000)
  | .elem .bool => .bool false
  | _ => .int 10000

def runAll : IO UInt32 := do
  let mut count := 0
  let mut failures := 0
  for tr in contract.transitions do
    let isInit := tr.name == "initialize"
    let args := if isInit then [addr 0x6000, addr 0x6000, addr 0x6001, addr 0x6001]
      else tr.params.map argument
    let sel := (Ethereum.KEC (String.toByteArray (transitionSigStr tr))).extract 0 4
    let cd := (ABI.encodeCallWithSelector? sel (transitionSignature tr).paramTypes args).getD .empty
    let c : Stele.DiffTest.Case :=
      { label := "successful " ++ tr.name
        σ := if isInit then diffTarget.world else seeded
        I := diffTarget.env diffTarget.runtime (EVM.address 0x2000) 0 cd true }
    let r := runCase diffTarget c
    count := count + 1
    if !r.verdict.isSuccess then failures := failures + 1
    IO.println s!"{ABI.printSignature (transitionSignature tr)}: {r.verdict.describe}"
  IO.println s!"Successful paths: {count - failures}/{count}, {failures} failures"
  return if failures == 0 then 0 else 1

end Benchmarks.CurveVault.SuccessfulPaths

def main : IO UInt32 := Benchmarks.CurveVault.SuccessfulPaths.runAll
