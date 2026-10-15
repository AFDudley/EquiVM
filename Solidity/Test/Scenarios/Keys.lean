import Solidity.Test.Harness
import Solidity.Test.Specs.Keys
import Solidity.Test.Fixtures.KeysSolc

/-! # Differential cases: mapping keys of every kind.

`string` / `bytes` keys from literals (short, empty, longer than a word, `hex"…"`), memory and
calldata arguments, a storage string, `string.concat`, nested mappings, and the generated getters;
enum, user-defined value type, contract, `bytes4`, `int256`, `bool` and `uint8` keys.  Pre-states
go through layout paths (`refs`), so the slot derivation is checked against solc on every read. -/

namespace Solidity.Test.Keys

open Solidity.Test Ethereum

def runtime : ByteArray := bytesOfHex Fixtures.keysRuntimeHex

def str (s : String) : Solm.Value := .bytes s.toUTF8
def bs (xs : List Nat) : Solm.Value := .bytes ⟨(xs.map UInt8.ofNat).toArray⟩
def u256 : Ty := .uint ⟨256, by decide⟩
/-- `m[k]` of the `string` / `bytes`-keyed mapping at `slot`: the element of type `vty` at the
    absolute slot `keccak256(k ++ slot)`. -/
def bkey (vty : Ty) (slot : UInt256) (k : ByteArray) : Solm.EvaledStorageRef :=
  absRef vty (bytesMappingSlot k slot).toNat
def bl (xs : List Nat) : ByteArray := ⟨(xs.map UInt8.ofNat).toArray⟩
def A (n : Nat) : Solm.Value := .address (addr n)
def b4 (xs : List Nat) : Solm.Value := .fixedBytes ⟨3, by decide⟩ (xs.map UInt8.ofNat)
def longS : String := "a very long key that does not fit in thirty-two bytes"

/-- A short `string` / `bytes` storage word: the bytes left-aligned, `2 * length` in the low byte. -/
def shortStr (s : String) : UInt256 :=
  let b := s.toUTF8.toList
  .ofNat (bytesToNatBE (b ++ List.replicate (31 - b.length) 0 ++ [UInt8.ofNat (2 * b.length)]))

def mk (sig : String) (args : List Solm.Value) (tag : String := "") (refs : List (Solm.EvaledStorageRef × Nat) := [])
    (storage : List (UInt256 × UInt256) := []) : Case :=
  { name := s!"{sig} {tag}", code := runtime, call := some (sig, args), refs := refs, storage := storage,
    expect := .success }

def byName (k : String) (v : Nat) : Solm.EvaledStorageRef × Nat := (bkey u256 ⟨0⟩ k.toUTF8, v)
def seen (xs : List Nat) : Solm.EvaledStorageRef × Nat := (bkey .bool ⟨1⟩ (bl xs), 1)
/-- `nested["a"][0x01]`: the inner mapping sits at `keccak256("a" ++ 2)`. -/
def nestedA1 (v : Nat) : Solm.EvaledStorageRef × Nat := (bkey u256 (bytesMappingSlot "a".toUTF8 ⟨2⟩) (bl [1]), v)

def cases : List Case :=
  [ mk "setByName(string,uint256)" [str "alice", .int 7],
    mk "setByName(string,uint256)" [str "", .int 3] "empty key",
    mk "setByName(string,uint256)" [str longS, .int 9] "long key",
    mk "setByName(string,uint256)" [str "alice", .int 0] "clear" (refs := [byName "alice" 7]),
    mk "setByNameCd(string,uint256)" [str "bob", .int 4],
    mk "setLit(uint256)" [.int 5],
    mk "setFromStorage(uint256)" [.int 6] "" (storage := [(⟨10⟩, shortStr "zed")]),
    mk "setName(string)" [str "zed"],
    mk "getByName(string)" [str "alice"] "" (refs := [byName "alice" 11]),
    mk "getByName(string)" [str "nobody"] "absent" (refs := [byName "alice" 11]),
    mk "getByName(string)" [str longS] "long" (refs := [byName longS 12]),
    mk "getLit()" [] "" (refs := [byName "alice" 13]),
    mk "byName(string)" [str "alice"] "getter" (refs := [byName "alice" 14]),
    mk "byName(string)" [str ""] "getter empty" (refs := [byName "" 15]),
    mk "sumKeys(string,string)" [str "a", str "b"] "" (refs := [byName "a" 1, byName "b" 2]),
    mk "del(string)" [str "alice"] "" (refs := [byName "alice" 7]),
    mk "bump(string)" [str "x"] "" (refs := [byName "x" 41]),
    mk "bump(string)" [str "x"] "from zero",
    mk "emptyKeys()" [] "" (refs := [byName "" 8, seen []]),
    mk "emptyKeys()" [] "zero",
    mk "longKey(uint256)" [.int 21],
    mk "concatKey(string,string,uint256)" [str "al", str "ice", .int 22],
    mk "mark(bytes)" [bs [1, 2, 3]],
    mk "mark(bytes)" [bs []] "empty",
    mk "markCd(bytes)" [bs [1, 2, 3]] "set",
    mk "markCd(bytes)" [bs [1, 2, 3]] "clear" (refs := [seen [1, 2, 3]]),
    mk "markBlob()" [] "" (storage := [(⟨11⟩, shortStr "blob")]),
    mk "setBlob(bytes)" [bs [9, 9]],
    mk "markHex()" [],
    mk "seen(bytes)" [bs [0xde, 0xad, 0xbe, 0xef]] "getter" (refs := [seen [0xde, 0xad, 0xbe, 0xef]]),
    mk "seen(bytes)" [bs [0xde, 0xad]] "getter absent" (refs := [seen [0xde, 0xad, 0xbe, 0xef]]),
    mk "setNested(string,bytes,uint256)" [str "a", bs [1], .int 5],
    mk "getNested(string,bytes)" [str "a", bs [1]] "" (refs := [nestedA1 6]),
    mk "nested(string,bytes)" [str "a", bs [1]] "getter" (refs := [nestedA1 6]),
    mk "setColor(uint8,uint256)" [.int 2, .int 30],
    mk "byColor(uint8)" [.int 2] "getter" (refs := [(⟨"byColor", [.mindex (.int 2)]⟩, 30)]),
    mk "setId(uint64,uint256)" [.int 77, .int 31],
    mk "byId(uint64)" [.int 77] "getter" (refs := [(⟨"byId", [.mindex (.int 77)]⟩, 31)]),
    mk "setContract(address,uint256)" [A 0xBEEF, .int 32],
    mk "setSelf(uint256)" [.int 33],
    mk "byContract(address)" [A 0xC0FFEE] "getter self" (refs := [(⟨"byContract", [.mindex (.address (addr 0xC0FFEE))]⟩, 33)]),
    mk "setSel(bytes4,uint256)" [b4 [0xde, 0xad, 0xbe, 0xef], .int 34],
    mk "bySel(bytes4)" [b4 [0xde, 0xad, 0xbe, 0xef]] "getter"
      (refs := [(⟨"bySel", [.mindex (.fixedBytes ⟨3, by decide⟩ [0xde, 0xad, 0xbe, 0xef])]⟩, 34)]),
    mk "setInt(int256,uint256)" [.int (-5), .int 35],
    mk "byInt(int256)" [.int (-5)] "getter" (refs := [(⟨"byInt", [.mindex (.int (-5))]⟩, 35)]),
    mk "setBool(bool,uint256)" [.bool true, .int 36],
    mk "byBool(bool)" [.bool false] "getter" (refs := [(⟨"byBool", [.mindex (.bool false)]⟩, 37)]),
    mk "setU8(uint8,uint256)" [.int 255, .int 38],
    mk "byU8(uint8)" [.int 9] "getter" (refs := [(⟨"byU8", [.mindex (.int 9)]⟩, 39)]) ]

def scenario : Scenario :=
  { name := "Keys", program := _root_.Keys.SoliditySpec.program, target := "Keys", cases := cases }

end Solidity.Test.Keys
