import Benchmarks.CurveVault.DiffTarget

open Solm Solm.DiffTest ABI Ethereum Ethereum.EVM
open Benchmarks.CurveVault

namespace Benchmarks.CurveVault.InitializeDiagnostic

def word (n : Nat) : ByteArray := (UInt256.ofNat n).toByteArray

/-- decimals() returns 18; symbol() returns the supplied bytes verbatim. -/
def token (out : ByteArray) : ByteArray :=
  ⟨#[0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x63, 0x95, 0xd8, 0x9b, 0x41,
     0x14, 0x60, 22, 0x57, 0x60, 18, 0x5f, 0x52, 0x60, 32, 0x5f, 0xf3,
     0x5b, 0x60, UInt8.ofNat out.size, 0x60, 33, 0x5f, 0x39,
     0x60, UInt8.ofNat out.size, 0x5f, 0xf3]⟩ ++ out

def run (len : Nat) (padding : UInt8) : IO Unit := do
  let data : ByteArray := ⟨Array.replicate len 0x41 ++ Array.replicate (32 - len) padding⟩
  let out := word 32 ++ word len ++ data
  let t := { diffTarget with callees := [(EVM.address 0x5000, token out)] }
  let args := [0x6000, 0x7000, 0x5000, 0x8000].map (fun n => Value.address (EVM.address n))
  let cd := (ABI.encodeCallWithSelector? ⟨#[0xf8, 0xc8, 0x76, 0x5e]⟩
    (initializeTransition.params.map Param.ty) args).getD .empty
  let c : Solm.DiffTest.Case :=
    { label := s!"symbol length={len}, padding={padding}"
      σ := t.world
      I := t.env t.runtime (EVM.address 0x2000) 0 cd true }
  let r := runCase t c
  IO.println s!"symbol length={len}, padding={padding}: {repr r.verdict}"
  if let some σ := r.postState then
    let a := (σ.get? t.selfAddress).getD default
    for slot in [6, 7, 8, 9, 10, 11] do
      let v := (a.storage.get? (UInt256.ofNat slot)).getD ⟨0⟩
      IO.println s!"  storage[{slot}] = 0x{String.ofList (Nat.toDigits 16 v.toNat)}"

end Benchmarks.CurveVault.InitializeDiagnostic

def main : IO Unit := do
  for n in [0, 1, 15, 16, 17, 30, 31, 32] do
    Benchmarks.CurveVault.InitializeDiagnostic.run n 0
  Benchmarks.CurveVault.InitializeDiagnostic.run 1 0xff
