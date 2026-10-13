import Solm.DiffTest.Harness

open Solm Solm.DiffTest ABI Ethereum Ethereum.EVM

namespace Benchmarks.CurveVault.Fixtures

def selector (n : Nat) : ByteArray := ⟨#[UInt8.ofNat (n / 2^24),
  UInt8.ofNat (n / 2^16), UInt8.ofNat (n / 2^8), UInt8.ofNat n]⟩

/-- Small fixture programs return the supplied bytes, including malformed ABI bytes. -/
def returnData (out : ByteArray) : ByteArray := Id.run do
  let mut code := ByteArray.empty
  for i in [:((out.size + 31) / 32)] do
    code := code ++ ⟨#[0x7f]⟩ ++ out.readWithPadding (i * 32) 32 ++
      ⟨#[0x60, UInt8.ofNat (i * 32), 0x52]⟩
  return code ++ ⟨#[0x60, UInt8.ofNat out.size, 0x5f, 0xf3]⟩

def mock (entries : List (Nat × ByteArray)) (fallback : ByteArray := wordBytes 1) : ByteArray := Id.run do
  let mut tests := ByteArray.empty
  let mut bodies := returnData fallback
  for (sel, out) in entries do
    let dest := entries.length * 15 + bodies.size
    tests := tests ++ ⟨#[0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x63]⟩ ++ selector sel ++
      ⟨#[0x14, 0x61, UInt8.ofNat (dest / 256), UInt8.ofNat dest, 0x57]⟩
    bodies := bodies ++ ⟨#[0x5b]⟩ ++ returnData out
  return tests ++ bodies

def token : ByteArray := mock
  [(0x313ce567, wordBytes 18),
   (0x95d89b41, wordBytes 32 ++ wordBytes 4 ++
     ("TEST".toUTF8 ++ ByteArray.zeroes 28))]

def controller : ByteArray := mock
  [(0x092314da, wordBytes 20000), (0x31dc3ca8, wordBytes 10000),
   (0x1b1800e3, wordBytes 0), (0x1059fcbd, wordBytes 0),
   (0x2c4e722e, wordBytes 1), (0xf851a440, wordBytes 0x2000)]

def callees : List (EVM.Address × ByteArray) :=
  [(EVM.address 0x6000, controller), (EVM.address 0x6001, token)]

end Benchmarks.CurveVault.Fixtures
