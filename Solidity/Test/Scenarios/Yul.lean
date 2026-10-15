import Solidity.Test.Harness
import Solidity.Test.Specs.Yul
import Solidity.Test.Fixtures.YulSolc

/-! # Differential cases: inline assembly (level 1).

`YulArith`: arithmetic, comparison and bit builtins, assignments to typed locals, `switch`, `if`,
nested blocks.  `YulEnv`: environment builtins, `calldataload`, `blockhash`.  `YulStore`: `sload` /
`sstore`, `tload` / `tstore`, `x.slot` / `x.offset`, storage pointers at absolute slots
(`StorageSlot`), constants, mapping and array slot derivation.  `YulMem`: words of memory objects,
scratch and free memory, `keccak256`, `mstore8`, custom reverts, `return` / `stop`.  `YulCall`:
`call` / `staticcall` / `delegatecall` through memory, the proxy fallback, `create` / `create2`,
`log2`.  `YulFlow`: `return` inside a modifier, a loop, an internal call. -/

namespace Solidity.Test.Yul

open Solidity.Test Ethereum

def arithRuntime : ByteArray := bytesOfHex Fixtures.yulArithRuntimeHex
def envRuntime : ByteArray := bytesOfHex Fixtures.yulEnvRuntimeHex
def storeRuntime : ByteArray := bytesOfHex Fixtures.yulStoreRuntimeHex
def memRuntime : ByteArray := bytesOfHex Fixtures.yulMemRuntimeHex
def callRuntime : ByteArray := bytesOfHex Fixtures.yulCallRuntimeHex
def flowRuntime : ByteArray := bytesOfHex Fixtures.yulFlowRuntimeHex
def targetRuntime : ByteArray := bytesOfHex Fixtures.targetRuntimeHex
def targetCreation : ByteArray := bytesOfHex Fixtures.targetCreationHex
def implRuntime : ByteArray := bytesOfHex Fixtures.implRuntimeHex

def MAX : Nat := 2 ^ 256 - 1
def A (n : Nat) : Stele.Value := .address (addr n)
def b32 (n : Nat) : Stele.Value := .fixedBytes ⟨31, by decide⟩ (wordBytes n).toList
def bs (xs : List Nat) : Stele.Value := .bytes ⟨(xs.map UInt8.ofNat).toArray⟩
def arr (xs : List Nat) : Stele.Value := .array (xs.map (.int ·))
def ints (xs : List Int) : List Stele.Value := xs.map (.int ·)

def mk (code : ByteArray) (sig : String) (args : List Stele.Value) (tag : String := "") : Case :=
  { name := s!"{sig} {tag}", code := code, call := some (sig, args) }

def ok (c : Case) : Case := { c with expect := .success }
def rv (c : Case) : Case := { c with expect := .revert }

/-! ## YulArith -/

def arithCases : List Case :=
  [ ok (mk arithRuntime "ops(uint256,uint256)" (ints [7, 3])),
    ok (mk arithRuntime "ops(uint256,uint256)" (ints [3, 7]) "y > x"),
    ok (mk arithRuntime "ops(uint256,uint256)" (ints [MAX, 0]) "zero divisor"),
    ok (mk arithRuntime "ops(uint256,uint256)" (ints [12345, 256]) "shift out"),
    ok (mk arithRuntime "ops(uint256,uint256)" (ints [2, 255]) "exp"),
    ok (mk arithRuntime "signed(int256,int256)" (ints [-7, 2])),
    ok (mk arithRuntime "signed(int256,int256)" (ints [7, -2])),
    ok (mk arithRuntime "signed(int256,int256)" (ints [-129, 0]) "zero divisor"),
    ok (mk arithRuntime "signed(int256,int256)" (ints [200, 300]) "positive"),
    ok (mk arithRuntime "mulDiv(uint256,uint256,uint256)" (ints [10, 20, 7]) "small"),
    ok (mk arithRuntime "mulDiv(uint256,uint256,uint256)" (ints [2 ^ 200, 2 ^ 100, 2 ^ 60]) "512-bit"),
    ok (mk arithRuntime "mulDiv(uint256,uint256,uint256)" (ints [MAX, MAX - 1, MAX]) "wide"),
    rv (mk arithRuntime "mulDiv(uint256,uint256,uint256)" (ints [2 ^ 200, 2 ^ 100, 2 ^ 40]) "overflow"),
    rv (mk arithRuntime "mulDiv(uint256,uint256,uint256)" (ints [3, 4, 0]) "zero"),
    ok (mk arithRuntime "ternary(bool,uint256,uint256)" [.bool true, .int 5, .int 9]),
    ok (mk arithRuntime "ternary(bool,uint256,uint256)" [.bool false, .int 5, .int 9]),
    ok (mk arithRuntime "small(uint256)" (ints [0x11223344556677889900112233445566778899aabbccddeeff00112233445566])),
    ok (mk arithRuntime "small(uint256)" (ints [7])),
    ok (mk arithRuntime "small(uint256)" (ints [MAX])),
    ok (mk arithRuntime "modOps(uint256,uint256,uint256)" (ints [MAX, MAX, 10])),
    ok (mk arithRuntime "modOps(uint256,uint256,uint256)" (ints [5, 6, 0]) "zero"),
    ok (mk arithRuntime "switchy(uint256)" (ints [0])), ok (mk arithRuntime "switchy(uint256)" (ints [1])),
    ok (mk arithRuntime "switchy(uint256)" (ints [2])), ok (mk arithRuntime "switchy(uint256)" (ints [50])) ]

/-! ## YulEnv -/

def C : Nat := 0xC0DE
def E : Nat := 0xE0A

def envAccounts : List (EVM.Address × Account) :=
  [ (addr C, account (balance := 77) (code := targetRuntime)) ]

def envHeader : BlockHeader :=
  { (default : BlockHeader) with
    timestamp := 1700000000, number := 19000000, beneficiary := addr 0xC01BA5E,
    gasLimit := 30000000, baseFeePerGas := 12, prevRandao := .ofNat 0xABCDEF }

/-- `n` earlier blocks with distinct hashes. -/
def blocksN (n : Nat) : ProcessedBlocks :=
  ((List.range n).map fun i => ({ hash := word (1000 + i), blockHeader := default, σ := ∅ } : ProcessedBlock)).toArray

def withTx (c : Case) : Case :=
  { c with value := 5, balance := 11, origin := some (addr 0x0121), gasPrice := 42, header := envHeader }

def envCases : List Case :=
  [ ok { mk envRuntime "env()" [] "plain" with accounts := envAccounts, header := envHeader },
    ok (withTx (mk envRuntime "env()" [] "value, origin, gasprice")),
    ok { mk envRuntime "acct(address)" [A C] "contract" with accounts := envAccounts },
    ok { mk envRuntime "acct(address)" [A E] "eoa" with accounts := envAccounts },
    ok { mk envRuntime "acct(address)" [A 0xA11CE] "sender" with accounts := envAccounts },
    ok (mk envRuntime "cdload(uint256)" (ints [0])), ok (mk envRuntime "cdload(uint256)" (ints [4])),
    ok (mk envRuntime "cdload(uint256)" (ints [20]) "partial"), ok (mk envRuntime "cdload(uint256)" (ints [100]) "beyond"),
    ok { name := "tail() appended sender", code := envRuntime,
         calldata := selectorOfSig "tail()" ++ ⟨((List.range 20).map fun i => UInt8.ofNat (0xA0 + i)).toArray⟩ },
    ok { (mk envRuntime "bh(uint256)" (ints [7]) "known") with header := { envHeader with number := 8 }, blocks := blocksN 8 },
    ok { (mk envRuntime "bh(uint256)" (ints [300]) "unknown") with header := { envHeader with number := 8 }, blocks := blocksN 8 } ]

/-! ## YulStore -/

def IMPL_SLOT : Nat := 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc
/-- Data slot of `arr` (slot 3). -/
def arrData : Nat := natOfBytes (KEC (wordBytes 3))

/-- `arr = [11, 22]`. -/
def withArr (c : Case) : Case :=
  { c with storage := [(⟨3⟩, ⟨2⟩), (.ofNat arrData, ⟨11⟩), (.ofNat (arrData + 1), ⟨22⟩)] }

def storeCases : List Case :=
  [ ok { mk storeRuntime "rawLoad(uint256)" (ints [0]) with refs := [(⟨"x", []⟩, 123)] },
    ok { mk storeRuntime "rawLoad(uint256)" (ints [1]) "packed" with refs := [(⟨"p1", []⟩, 5), (⟨"p2", []⟩, 6)] },
    ok (mk storeRuntime "rawLoad(uint256)" (ints [99]) "empty"),
    ok (mk storeRuntime "rawStore(uint256,uint256)" (ints [0, 55])),
    ok (mk storeRuntime "rawStore(uint256,uint256)" (ints [1, 2 ^ 64 + 3]) "packed"),
    ok (mk storeRuntime "slots()" []),
    ok (mk storeRuntime "setImpl(address)" [A 0xBEEF]),
    ok { mk storeRuntime "getImpl()" [] with storage := [(.ofNat IMPL_SLOT, .ofNat 0xBEEF)] },
    ok (mk storeRuntime "getImpl()" [] "unset"),
    ok (mk storeRuntime "setAt(bytes32,uint256)" [b32 0x77, .int 9]),
    ok { mk storeRuntime "getAt(bytes32)" [b32 0x77] with storage := [(.ofNat 0x77, .ofNat 9)] },
    ok (mk storeRuntime "consts()" []),
    ok (mk storeRuntime "balSlot(address)" [A 0xB0B]),
    ok { mk storeRuntime "bal(address)" [A 0xB0B] with refs := [(⟨"bal", [.mindex (.address (addr 0xB0B))]⟩, 31)] },
    ok (withArr (mk storeRuntime "unsafeAccess(uint256)" (ints [1]))),
    ok (withArr (mk storeRuntime "unsafeAccess(uint256)" (ints [5]) "past the end")),
    ok (withArr (mk storeRuntime "arr(uint256)" (ints [1]))),
    ok (mk storeRuntime "pushArr(uint256)" (ints [8])),
    ok { mk storeRuntime "pairSlot()" [] with refs := [(⟨"pair", [.field "a"]⟩, 3), (⟨"pair", [.field "b"]⟩, 4)] },
    ok (mk storeRuntime "setPair(uint128,uint128)" (ints [1, 2])),
    ok (mk storeRuntime "tstore_(uint256,uint256)" (ints [5, 44])) ]

/-! ## YulMem -/

def sig65 : List Nat := (List.range 65).map fun i => (i * 7 + 1) % 256

def memCases : List Case :=
  [ ok (mk memRuntime "bytesLen(bytes)" [bs [1, 2, 3]]), rv (mk memRuntime "bytesLen(bytes)" [bs []] "empty"),
    ok (mk memRuntime "bytesLen(bytes)" [bs ((List.range 40).map (· + 100))] "long"),
    ok (mk memRuntime "split(bytes)" [bs sig65]), rv (mk memRuntime "split(bytes)" [bs [1, 2]] "short"),
    ok (mk memRuntime "selectorOf(bytes)" [bs [0xa9, 0x05, 0x9c, 0xbb, 1, 2, 3]]),
    rv (mk memRuntime "selectorOf(bytes)" [bs [0xa9, 0x05]] "short"),
    rv (mk memRuntime "elem(uint256[],uint256)" [arr [10, 20, 30], .int 3] "oob"),
    rv (mk memRuntime "shrink(bytes,uint256)" [bs [1, 2], .int 3] "grow"),
    ok (mk memRuntime "elem(uint256[],uint256)" [arr [10, 20, 30], .int 1]),
    ok (mk memRuntime "elem(uint256[],uint256)" [arr [10, 20, 30], .int 0]),
    ok (mk memRuntime "setElem(uint256[],uint256,uint256)" [arr [10, 20, 30], .int 2, .int 99]),
    ok (mk memRuntime "shrink(bytes,uint256)" [bs [1, 2, 3, 4, 5], .int 2]),
    ok (mk memRuntime "shrink(bytes,uint256)" [bs [1, 2, 3, 4, 5], .int 0] "to empty"),
    ok (mk memRuntime "fields((uint256,address,bytes))" [.tuple [.int 9, A 0xB0B, bs [1, 2, 3, 4]]]),
    ok (mk memRuntime "hashPair(bytes32,bytes32)" [b32 1, b32 2]),
    ok (mk memRuntime "toEthSignedMessageHash(bytes32)" [b32 0x1234]),
    ok (mk memRuntime "toTypedDataHash(bytes32,bytes32)" [b32 0xAAAA, b32 0xBBBB]),
    ok (mk memRuntime "computeAddress(bytes32,bytes32,address)" [b32 1, b32 2, A 0xDE91]),
    ok (mk memRuntime "hashMem(bytes)" [bs [5, 6, 7]]), ok (mk memRuntime "hashMem(bytes)" [bs []] "empty"),
    ok (mk memRuntime "hashMem(bytes)" [bs ((List.range 70).map (· * 3 % 256))] "long"),
    rv (mk memRuntime "bubble(bytes)" [bs [8, 0xc3, 0x79, 0xa0, 1]]), rv (mk memRuntime "bubble(bytes)" [bs []] "empty"),
    rv (mk memRuntime "panicWith(uint256)" (ints [0x11])), rv (mk memRuntime "panicWith(uint256)" (ints [0x32])),
    ok (mk memRuntime "retWord(uint256)" (ints [77])),
    ok (mk memRuntime "retBytes(bytes)" [bs [1, 2, 3]]), ok (mk memRuntime "retBytes(bytes)" [bs []] "empty"),
    ok (mk memRuntime "stopper(uint256)" (ints [0]) "stop"), ok (mk memRuntime "stopper(uint256)" (ints [5]) "return"),
    ok (mk memRuntime "freeBump()" []) ]

/-! ## YulCall -/

def T : Nat := 0x7A26E7
def I : Nat := 0x1A91
def S : Nat := 0x5EED

def callAccounts : List (EVM.Address × Account) :=
  [ (addr T, account (balance := 3) (code := targetRuntime)), (addr I, account (code := implRuntime)) ]

def enc (sig : String) (args : List Nat) : Stele.Value :=
  bs ((selectorOfSig sig ++ (args.foldl (fun b w => b ++ wordBytes w) ByteArray.empty)).toList.map (·.toNat))

def mkC (sig : String) (args : List Stele.Value) (tag : String := "") (value : Nat := 0) (funds : Nat := 0) : Case :=
  let c := mk callRuntime sig args tag
  { c with accounts := callAccounts, value := value, balance := funds + value, storage := [(⟨0⟩, .ofNat I)] }

/-- A message to the proxy (no matching selector, or empty calldata): delegated to `Impl`. -/
def proxy (cd : ByteArray) (tag : String) (value : Nat := 0) : Case :=
  { name := s!"proxy {tag}", code := callRuntime, calldata := cd, accounts := callAccounts, value := value, balance := value, storage := [(⟨0⟩, .ofNat I)] }

def callCases : List Case :=
  [ ok (mkC "sendValue(address,uint256)" [A T, .int 2] "funded" (value := 5)),
    ok (mkC "sendValue(address,uint256)" [A S, .int 2] "to eoa" (value := 5)),
    ok (mkC "sendValue(address,uint256)" [A T, .int 9] "insufficient" (value := 5)),
    ok (mkC "rawCall(address,bytes)" [A T, enc "set(uint256)" [5]] "set"),
    ok (mkC "rawCall(address,bytes)" [A T, enc "set(uint256)" [5]] "set with value" (value := 3)),
    ok (mkC "rawCall(address,bytes)" [A T, enc "fail(uint256)" [1]] "revert data"),
    ok (mkC "rawCall(address,bytes)" [A T, enc "fail(uint256)" [0]] "no return data"),
    ok (mkC "rawCall(address,bytes)" [A S, enc "set(uint256)" [5]] "eoa"),
    ok (mkC "staticWord(address,bytes)" [A T, enc "twice(uint256)" [21]]),
    ok (mkC "staticWord(address,bytes)" [A T, enc "set(uint256)" [21]] "write in static"),
    ok (mkC "staticWord(address,bytes)" [A T, enc "last()" []]),
    ok (mkC "gasCapped(address,bytes,uint256)" [A T, enc "set(uint256)" [5], .int 200000] "enough"),
    ok (mkC "gasCapped(address,bytes,uint256)" [A T, enc "set(uint256)" [5], .int 2000] "too little"),
    ok (proxy (selectorOfSig "set(uint256)" ++ wordBytes 41) "set"),
    ok (proxy (selectorOfSig "set(uint256)" ++ wordBytes 41) "set with value" (value := 2)),
    rv (proxy (selectorOfSig "fail(uint256)" ++ wordBytes 1) "fail"),
    ok (proxy (selectorOfSig "fail(uint256)" ++ wordBytes 0) "fail ok"),
    ok (proxy ByteArray.empty "receive" (value := 4)),
    rv (proxy (selectorOfSig "nothing()") "unknown selector"),
    ok (mkC "clone(address)" [A T]),
    ok (mkC "cloneDeterministic(address,bytes32)" [A T, b32 0x5A17]),
    ok (mkC "deploy(bytes,bytes32,uint256)" [bs (targetCreation.toList.map (·.toNat)), b32 1, .int 0]),
    ok (mkC "deploy(bytes,bytes32,uint256)" [bs (targetCreation.toList.map (·.toNat)), b32 1, .int 1] "with value" (value := 1)),
    ok (mkC "deploy(bytes,bytes32,uint256)" [bs [0xfe], b32 2, .int 0] "init code reverts"),
    ok (mkC "logIt(uint256,uint256)" (ints [3, 4])) ]

/-! ## YulFlow -/

def flowCases : List Case :=
  [ ok { mk flowRuntime "early(uint256)" (ints [3]) "halts" with refs := [(⟨"n", []⟩, 1000)] },
    ok { mk flowRuntime "early(uint256)" (ints [2]) "returns" with refs := [(⟨"n", []⟩, 1000)] },
    ok (mk flowRuntime "inLoop(uint256)" (ints [4])), ok (mk flowRuntime "inLoop(uint256)" (ints [0])),
    ok (mk flowRuntime "inLoop(uint256)" (ints [12]) "never"),
    ok (mk flowRuntime "viaCall(uint256)" (ints [7]) "halts"), ok (mk flowRuntime "viaCall(uint256)" (ints [1]) "returns"),
    ok (mk flowRuntime "revertIn(uint256)" (ints [1])), rv (mk flowRuntime "revertIn(uint256)" (ints [3])) ]

def scenarios : List Scenario :=
  [ { name := "YulArith", program := _root_.Yul.SoliditySpec.program, target := "YulArith", cases := arithCases },
    { name := "YulEnv", program := _root_.Yul.SoliditySpec.program, target := "YulEnv", cases := envCases },
    { name := "YulStore", program := _root_.Yul.SoliditySpec.program, target := "YulStore", cases := storeCases },
    { name := "YulMem", program := _root_.Yul.SoliditySpec.program, target := "YulMem", cases := memCases },
    { name := "YulCall", program := _root_.Yul.SoliditySpec.program, target := "YulCall", cases := callCases },
    { name := "YulFlow", program := _root_.Yul.SoliditySpec.program, target := "YulFlow", cases := flowCases } ]

end Solidity.Test.Yul
