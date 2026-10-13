import Benchmarks.CurveVault.DiffTarget

open Stele Stele.DiffTest Stele.Interp ABI Ethereum Ethereum.EVM
open Benchmarks.CurveVault

namespace Benchmarks.CurveVault.BoundaryCases

def addr (n : Nat) : Value := .address (EVM.address n)

def withSlots (t : Target) (slots : List (Nat × Nat)) : AccountMap := Id.run do
  let I := t.env t.runtime (EVM.address 0x2000) 0 .empty true
  let mut evm := initialState t.world t.world (UInt256.ofNat t.gas) default I
  for (slot, value) in slots do
    evm := EVM.storageStore evm t.selfAddress (UInt256.ofNat slot) (UInt256.ofNat value)
  return evm.accountMap

def initializedSlots : List (Nat × Nat) :=
  [(0, 0x6001), (1, 0x6001), (2, 0x6000), (3, 0x6000), (4, 0x6000),
   (5, 2^256-1), (14, 100000), (15, 1)]

def check (t : Target) (label : String) (σ : AccountMap) (cd : ByteArray)
    (expectedOOG : Bool := false) : IO Nat := do
  let c : Stele.DiffTest.Case :=
    { label, σ, I := t.env t.runtime (EVM.address 0x2000) 0 cd true }
  let r := runCase t c
  IO.println s!"{label}: {r.verdict.describe}"
  let ok := if expectedOOG then match r.verdict with
    | .evmOutOfGas => true
    | _ => false
    else r.verdict.isAgree
  return if ok then 0 else 1

def initializeData : ByteArray :=
  (ABI.encodeCallWithSelector? (Fixtures.selector 0xf8c8765e)
    (initializeTransition.params.map Param.ty)
    [addr 0x6000, addr 0x6000, addr 0x6001, addr 0x6001]).getD .empty

def runAll : IO UInt32 := do
  let mut failures := 0
  let mut count := 0
  -- Both getters use the same three-word bound, even though symbol's source capacity is 34.
  for (getter, sel, slot) in [("name", 0x06fdde03, 6), ("symbol", 0x95d89b41, 9)] do
    for len in [0, 1, 31, 32, 33, 34, 35, 63, 64, 65, 96, 97,
        2^256-64, 2^256-63, 2^256-33, 2^256-32, 2^256-31, 2^256-1] do
      let σ := withSlots diffTarget [(slot, len), (slot+1, 2^256-1), (slot+2, 2^256-1)]
      failures := failures + (← check diffTarget s!"{getter} header={len}" σ
        (Fixtures.selector sel) (len > 2^256-32))
      count := count + 1
  -- Arbitrary offsets, truncations, capacity violations and dirty padding on symbol().
  for offset in [0, 1, 31, 32, 33, 63, 64, 65, 2^256-1] do
    for len in [0, 1, 32, 33] do
      let out := wordBytes offset ++ wordBytes len ++ wordBytes (2^256-1)
      let t := { diffTarget with callees := [(EVM.address 0x6001,
        Fixtures.mock [(0x313ce567, wordBytes 18), (0x95d89b41, out)])] }
      failures := failures + (← check t s!"symbol offset={offset} length={len}" t.world initializeData)
      count := count + 1
  for size in [0, 1, 31, 32, 33, 63, 64, 65, 95, 96, 97] do
    let out := (wordBytes 32 ++ wordBytes 1 ++ wordBytes (2^256-1) ++ wordBytes 1).extract 0 size
    let t := { diffTarget with callees := [(EVM.address 0x6001,
      Fixtures.mock [(0x313ce567, wordBytes 18), (0x95d89b41, out)])] }
    failures := failures + (← check t s!"symbol return bytes={size}" t.world initializeData)
    count := count + 1
  for decimals in [0, 18, 19, 255, 256, 2^256-1] do
    let t := { diffTarget with callees := [(EVM.address 0x6001,
      Fixtures.mock [(0x313ce567, wordBytes decimals),
        (0x95d89b41, wordBytes 32 ++ wordBytes 0 ++ wordBytes 0)])] }
    failures := failures + (← check t s!"decimals={decimals}" t.world initializeData)
    count := count + 1
  let depositData := Fixtures.selector 0xb6b55f25 ++ wordBytes 10000
  for out in [ByteArray.empty, ⟨#[1]⟩, wordBytes 0, wordBytes 1, wordBytes 2,
      wordBytes 1 ++ wordBytes (2^256-1)] do
    let t := { diffTarget with callees := [(EVM.address 0x6000, Fixtures.controller),
      (EVM.address 0x6001, Fixtures.returnData out)] }
    failures := failures + (← check t s!"transferFrom return={repr out}" (withSlots t initializedSlots) depositData)
    count := count + 1
  let codeless := { diffTarget with callees := [(EVM.address 0x6000, Fixtures.controller)] }
  failures := failures + (← check codeless "codeless transferFrom, nonzero amount"
    (withSlots codeless initializedSlots) depositData)
  failures := failures + (← check codeless "codeless transferFrom, zero amount"
    (withSlots codeless initializedSlots) (Fixtures.selector 0x2e1a7d4d ++ wordBytes 0))
  count := count + 2
  -- A controller word re-read after mapping writes must retain its high bits in
  -- transferFrom calldata. The EVM call target still uses its low 160 bits.
  let rawController := 2^160 + 0x6000
  let checkRecipient := (⟨#[0x60, 0x24, 0x35, 0x7f]⟩ : ByteArray) ++
    wordBytes rawController ++ ⟨#[0x14, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩
  let t := { diffTarget with callees := [(EVM.address 0x6000, Fixtures.controller),
    (EVM.address 0x6001, checkRecipient)] }
  failures := failures + (← check t "raw controller word in transferFrom calldata"
    (withSlots t (initializedSlots ++ [(3, rawController)])) depositData)
  count := count + 1
  for (label, entries, sel) in
      [("assets addition overflow", [(0x092314da, wordBytes (2^256-1)), (0x31dc3ca8, wordBytes 1)], 0x01e1d114),
       ("APR multiplication overflow", [(0x31dc3ca8, wordBytes 1), (0x2c4e722e, wordBytes (2^256-1))], 0xa980497e)] do
    let t := { diffTarget with callees := [(EVM.address 0x6000, Fixtures.mock entries)] }
    failures := failures + (← check t label (withSlots t initializedSlots) (Fixtures.selector sel))
    count := count + 1
  IO.println s!"Boundary cases: {count}, {failures} failures (4 expected EVM out-of-gas cases)"
  return if failures == 0 then 0 else 1

end Benchmarks.CurveVault.BoundaryCases

def main : IO UInt32 := Benchmarks.CurveVault.BoundaryCases.runAll
