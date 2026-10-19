import Solidity.Syntax.Notation

/-! Yul (`Solidity/Test/Fixtures/Yul.sol`): inline assembly, level 1.  Harness input only. -/

namespace Yul.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def yulArith : SourceUnit := sol% contract YulArith {
  function ops(uint256 x, uint256 y) external pure returns (uint256[16] memory r) {
    assembly {
      mstore(r, add(x, y))
      mstore(add(r, 32), sub(x, y))
      mstore(add(r, 64), mul(x, y))
      mstore(add(r, 96), div(x, y))
      mstore(add(r, 128), mod(x, y))
      mstore(add(r, 160), exp(x, y))
      mstore(add(r, 192), and(x, y))
      mstore(add(r, 224), or(x, y))
      mstore(add(r, 256), xor(x, y))
      mstore(add(r, 288), not(x))
      mstore(add(r, 320), shl(y, x))
      mstore(add(r, 352), shr(y, x))
      mstore(add(r, 384), lt(x, y))
      mstore(add(r, 416), gt(x, y))
      mstore(add(r, 448), eq(x, y))
      mstore(add(r, 480), iszero(x))
    }
  }

  function signed(int256 x, int256 y) external pure returns (int256 q, int256 m, int256 s, uint256 lt_, uint256 gt_, int256 se) {
    assembly {
      q := sdiv(x, y)
      m := smod(x, y)
      s := sar(3, x)
      lt_ := slt(x, y)
      gt_ := sgt(x, y)
      se := signextend(0, x)
    }
  }

  function mulDiv(uint256 x, uint256 y, uint256 d) external pure returns (uint256 result) {
    uint256 prod0;
    uint256 prod1;
    assembly {
      let mm := mulmod(x, y, not(0))
      prod0 := mul(x, y)
      prod1 := sub(sub(mm, prod0), lt(mm, prod0))
    }
    if (prod1 == 0) {
      return prod0 / d;
    }
    require(d > prod1, "overflow");
    unchecked {
      uint256 remainder;
      assembly {
        remainder := mulmod(x, y, d)
        prod1 := sub(prod1, gt(remainder, prod0))
        prod0 := sub(prod0, remainder)
      }
      uint256 twos = d & (0 - d);
      assembly {
        d := div(d, twos)
        prod0 := div(prod0, twos)
        twos := add(div(sub(0, twos), twos), 1)
      }
      prod0 |= prod1 * twos;
      uint256 inverse = (3 * d) ^ 2;
      inverse *= 2 - d * inverse;
      inverse *= 2 - d * inverse;
      inverse *= 2 - d * inverse;
      inverse *= 2 - d * inverse;
      inverse *= 2 - d * inverse;
      inverse *= 2 - d * inverse;
      result = prod0 * inverse;
    }
  }

  function ternary(bool c, uint256 a, uint256 b) external pure returns (uint256 r) {
    assembly {
      r := xor(b, mul(xor(a, b), c))
    }
  }

  function small(uint256 w) external pure returns (uint8 a, bool b, address c, bytes4 d, bytes32 e) {
    assembly {
      a := byte(31, w)
      b := gt(w, 10)
      c := shr(96, shl(96, w))
      d := shl(224, w)
      e := w
    }
  }

  function modOps(uint256 a, uint256 b, uint256 n) external pure returns (uint256 x, uint256 y) {
    assembly {
      x := addmod(a, b, n)
      y := mulmod(a, b, n)
    }
  }

  function switchy(uint256 x) external pure returns (uint256 r) {
    assembly {
      switch x
      case 0 { r := 100 }
      case 1 { r := 200 }
      default { r := add(x, 1000) }
      if gt(r, 1001) { r := 7 }
      let t := 3
      {
        let t2 := add(t, 1)
        r := add(r, t2)
      }
      r := add(r, t)
    }
  }
}

def yulEnv : SourceUnit := sol% contract YulEnv {
  function env() external payable returns (uint256[14] memory r) {
    assembly {
      mstore(r, caller())
      mstore(add(r, 32), callvalue())
      mstore(add(r, 64), calldatasize())
      mstore(add(r, 96), origin())
      mstore(add(r, 128), gasprice())
      mstore(add(r, 160), address())
      mstore(add(r, 192), selfbalance())
      mstore(add(r, 224), chainid())
      mstore(add(r, 256), timestamp())
      mstore(add(r, 288), number())
      mstore(add(r, 320), coinbase())
      mstore(add(r, 352), gaslimit())
      mstore(add(r, 384), basefee())
      mstore(add(r, 416), prevrandao())
    }
  }

  function acct(address a) external view returns (uint256 bal, uint256 size, bytes32 hash) {
    assembly {
      bal := balance(a)
      size := extcodesize(a)
      hash := extcodehash(a)
    }
  }

  function cdload(uint256 off) external pure returns (bytes32 w, uint256 len) {
    assembly {
      w := calldataload(off)
      len := calldatasize()
    }
  }

  function tail() external pure returns (address sender) {
    assembly {
      sender := shr(96, calldataload(sub(calldatasize(), 20)))
    }
  }

  function bh(uint256 n) external view returns (bytes32 h) {
    assembly { h := blockhash(n) }
  }
}

def yulStore : SourceUnit := sol% contract YulStore {
  struct AddressSlot { address value; }
  struct Uint256Slot { uint256 value; }
  struct Pair { uint128 a; uint128 b; }

  uint256 public x;
  uint64 public p1;
  uint64 public p2;
  mapping(address => uint256) public bal;
  uint256[] public arr;
  Pair public pair;

  bytes32 internal constant IMPL_SLOT = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;
  uint256 internal constant SEVEN = 7;

  function rawLoad(uint256 slot) external view returns (uint256 v) {
    assembly { v := sload(slot) }
  }

  function rawStore(uint256 slot, uint256 v) external {
    assembly { sstore(slot, v) }
  }

  function slots() external pure returns (uint256 sx, uint256 s1, uint256 o1, uint256 s2, uint256 o2, uint256 sb, uint256 sa, uint256 sp) {
    assembly {
      sx := x.slot
      s1 := p1.slot
      o1 := p1.offset
      s2 := p2.slot
      o2 := p2.offset
      sb := bal.slot
      sa := arr.slot
      sp := pair.slot
    }
  }

  function getAddressSlot(bytes32 slot) internal pure returns (AddressSlot storage r) {
    assembly ("memory-safe") { r.slot := slot }
  }

  function getUint256Slot(bytes32 slot) internal pure returns (Uint256Slot storage r) {
    assembly ("memory-safe") { r.slot := slot }
  }

  function setImpl(address a) external {
    getAddressSlot(IMPL_SLOT).value = a;
  }

  function getImpl() external view returns (address) {
    return getAddressSlot(IMPL_SLOT).value;
  }

  function setAt(bytes32 slot, uint256 v) external {
    getUint256Slot(slot).value = v;
  }

  function getAt(bytes32 slot) external view returns (uint256) {
    return getUint256Slot(slot).value;
  }

  function consts() external pure returns (bytes32 r, uint256 s) {
    assembly {
      r := IMPL_SLOT
      s := SEVEN
    }
  }

  function balSlot(address k) external pure returns (bytes32 slot) {
    assembly {
      mstore(0x00, k)
      mstore(0x20, bal.slot)
      slot := keccak256(0x00, 0x40)
    }
  }

  function unsafeAccess(uint256 pos) external view returns (uint256 v) {
    uint256[] storage a = arr;
    bytes32 slot;
    assembly {
      mstore(0, a.slot)
      slot := add(keccak256(0, 0x20), pos)
    }
    return getUint256Slot(slot).value;
  }

  function pushArr(uint256 v) external { arr.push(v); }

  function pairSlot() external view returns (uint256 s, uint256 o, uint256 raw) {
    Pair storage q = pair;
    assembly {
      s := q.slot
      o := q.offset
      raw := sload(q.slot)
    }
  }

  function setPair(uint128 a, uint128 b) external { pair = Pair(a, b); }

  function tstore_(uint256 k, uint256 v) external returns (uint256 before, uint256 after_) {
    assembly {
      before := tload(k)
      tstore(k, v)
      after_ := tload(k)
    }
  }
}

def yulMem : SourceUnit := sol% contract YulMem {
  struct S { uint256 a; address b; bytes c; }

  function bytesLen(bytes memory b) external pure returns (uint256 len, bytes32 first) {
    require(b.length > 0, "empty");
    assembly {
      len := mload(b)
      first := mload(add(b, 32))
    }
  }

  function split(bytes memory sig) external pure returns (bytes32 r, bytes32 s, uint8 v) {
    require(sig.length == 65, "len");
    assembly ("memory-safe") {
      r := mload(add(sig, 0x20))
      s := mload(add(sig, 0x40))
      v := byte(0, mload(add(sig, 0x60)))
    }
  }

  function selectorOf(bytes memory data) external pure returns (bytes4 sel) {
    require(data.length >= 4, "short");
    assembly { sel := mload(add(data, 32)) }
  }

  function elem(uint256[] memory a, uint256 i) external pure returns (uint256 v, uint256 n) {
    require(i < a.length, "oob");
    assembly {
      n := mload(a)
      v := mload(add(add(a, 0x20), mul(i, 0x20)))
    }
  }

  function setElem(uint256[] memory a, uint256 i, uint256 v) external pure returns (uint256[] memory) {
    require(i < a.length, "oob");
    assembly { mstore(add(add(a, 0x20), mul(i, 0x20)), v) }
    return a;
  }

  function shrink(bytes memory b, uint256 n) external pure returns (bytes memory) {
    require(n <= b.length, "grow");
    assembly { mstore(b, n) }
    return b;
  }

  function fields(S memory s) external pure returns (uint256 a, address b, uint256 clen) {
    assembly {
      a := mload(s)
      b := mload(add(s, 32))
      clen := mload(mload(add(s, 64)))
    }
  }

  function hashPair(bytes32 a, bytes32 b) external pure returns (bytes32 h) {
    assembly {
      mstore(0x00, a)
      mstore(0x20, b)
      h := keccak256(0x00, 0x40)
    }
  }

  function toEthSignedMessageHash(bytes32 messageHash) external pure returns (bytes32 digest) {
    assembly ("memory-safe") {
      mstore(0x00, "\x19Ethereum Signed Message:\n32")
      mstore(0x1c, messageHash)
      digest := keccak256(0x00, 0x3c)
    }
  }

  function toTypedDataHash(bytes32 domainSeparator, bytes32 structHash) external pure returns (bytes32 digest) {
    assembly ("memory-safe") {
      let ptr := mload(0x40)
      mstore(ptr, hex"19_01")
      mstore(add(ptr, 0x02), domainSeparator)
      mstore(add(ptr, 0x22), structHash)
      digest := keccak256(ptr, 0x42)
    }
  }

  function computeAddress(bytes32 salt, bytes32 bytecodeHash, address deployer) external pure returns (address addr) {
    assembly ("memory-safe") {
      let ptr := mload(0x40)
      mstore(add(ptr, 0x40), bytecodeHash)
      mstore(add(ptr, 0x20), salt)
      mstore(ptr, deployer)
      let start := add(ptr, 0x0b)
      mstore8(start, 0xff)
      addr := keccak256(start, 85)
    }
  }

  function hashMem(bytes memory b) external pure returns (bytes32 h) {
    assembly { h := keccak256(add(b, 32), mload(b)) }
  }

  function bubble(bytes memory returndata) external pure {
    assembly ("memory-safe") {
      revert(add(32, returndata), mload(returndata))
    }
  }

  function panicWith(uint256 code) external pure {
    assembly ("memory-safe") {
      mstore(0x00, 0x4e487b71)
      mstore(0x20, code)
      revert(0x1c, 0x24)
    }
  }

  function retWord(uint256 v) external pure returns (uint256) {
    assembly {
      let ptr := mload(0x40)
      mstore(ptr, v)
      return(ptr, 0x20)
    }
  }

  function retBytes(bytes memory b) external pure returns (bytes memory) {
    assembly { return(add(b, 32), mload(b)) }
  }

  function stopper(uint256 v) external returns (uint256) {
    if (v == 0) { assembly { stop() } }
    return v;
  }

  function freeBump() external pure returns (uint256 r) {
    assembly {
      let ptr := mload(0x40)
      mstore(ptr, 7)
      mstore(0x40, add(ptr, 0x20))
      r := mload(ptr)
    }
    r += 1;
  }
}

def target : SourceUnit := sol% contract Target {
  uint256 public last;
  event Got(uint256 v);
  function set(uint256 v) external payable returns (uint256) { last = v; emit Got(v); return v + 1; }
  function fail(uint256 v) external pure { require(v == 0, "bad"); }
  function twice(uint256 v) external pure returns (uint256, uint256) { return (v, 2 * v); }
  receive() external payable {}
}

def yulCall : SourceUnit := sol% contract YulCall {
  address public impl;
  uint256 public last;

  constructor(address i) { impl = i; }

  function sendValue(address «to», uint256 amount) external payable returns (bool ok) {
    assembly { ok := call(gas(), «to», amount, 0, 0, 0, 0) }
  }

  function rawCall(address t, bytes memory data) external payable returns (bool ok, bytes32 w, uint256 n) {
    assembly {
      ok := call(gas(), t, callvalue(), add(data, 32), mload(data), 0, 0)
      n := returndatasize()
      if gt(n, 31) {
        returndatacopy(0, 0, 32)
        w := mload(0)
      }
    }
  }

  function staticWord(address t, bytes memory data) external view returns (bool ok, uint256 w, uint256 n) {
    assembly {
      ok := staticcall(gas(), t, add(data, 32), mload(data), 0x00, 0x20)
      n := returndatasize()
      if gt(n, 31) { w := mload(0x00) }
    }
  }

  function gasCapped(address t, bytes memory data, uint256 g) external returns (bool ok) {
    assembly { ok := call(g, t, 0, add(data, 32), mload(data), 0, 0) }
  }

  function _delegate(address implementation) internal {
    assembly {
      calldatacopy(0, 0, calldatasize())
      let result := delegatecall(gas(), implementation, 0, calldatasize(), 0, 0)
      returndatacopy(0, 0, returndatasize())
      switch result
      case 0 { revert(0, returndatasize()) }
      default { return(0, returndatasize()) }
    }
  }

  function _fallback() internal {
    _delegate(impl);
  }

  fallback() external payable { _fallback(); }
  receive() external payable { _fallback(); }

  function clone(address implementation) external returns (address «instance») {
    assembly ("memory-safe") {
      mstore(0x00, or(shr(0xe8, shl(0x60, implementation)), 0x602d8060093d393df3363d3d373d3d3d363d73))
      mstore(0x20, or(shl(0x78, implementation), 0x5af43d82803e903d91602b57fd5bf3))
      «instance» := create(0, 0x09, 0x37)
    }
    require(«instance» != address(0), "failed");
  }

  function cloneDeterministic(address implementation, bytes32 salt) external returns (address «instance») {
    assembly ("memory-safe") {
      mstore(0x00, or(shr(0xe8, shl(0x60, implementation)), 0x602d8060093d393df3363d3d373d3d3d363d73))
      mstore(0x20, or(shl(0x78, implementation), 0x5af43d82803e903d91602b57fd5bf3))
      «instance» := create2(0, 0x09, 0x37, salt)
    }
    require(«instance» != address(0), "failed");
  }

  function deploy(bytes memory code, bytes32 salt, uint256 amount) external payable returns (address addr) {
    assembly ("memory-safe") {
      addr := create2(amount, add(code, 0x20), mload(code), salt)
    }
  }

  function logIt(uint256 a, uint256 b) external {
    assembly {
      mstore(0x00, b)
      log2(0x00, 0x20, 0x1234, a)
    }
  }
}

def impl : SourceUnit := sol% contract Impl {
  address public impl;
  uint256 public last;
  function set(uint256 v) external payable returns (uint256) { last = v; return v + 1; }
  function fail(uint256 v) external pure { require(v == 0, "nope"); }
  receive() external payable { last = 1; }
}

def yulFlow : SourceUnit := sol% contract YulFlow {
  uint256 public n;

  modifier guard() {
    n += 1;
    _;
    n += 100;
  }

  function early(uint256 v) external guard returns (uint256) {
    n += 10;
    if (v == 3) {
      assembly { mstore(0, 42) return(0, 32) }
    }
    return v;
  }

  function inLoop(uint256 k) external returns (uint256) {
    for (uint256 i = 0; i < 10; i++) {
      n += 1;
      if (i == k) {
        unchecked {
          assembly { mstore(0, i) return(0, 32) }
        }
      }
    }
    return 99;
  }

  function viaCall(uint256 v) external returns (uint256) {
    helper(v);
    return 5;
  }

  function helper(uint256 v) internal {
    if (v > 1) {
      assembly { mstore(0, v) return(0, 32) }
    }
    n += v;
  }

  function revertIn(uint256 v) external {
    n = v;
    assembly {
      if gt(v, 2) { revert(0, 0) }
    }
  }
}

def program : Program := [yulArith, yulEnv, yulStore, yulMem, target, yulCall, impl, yulFlow]

end Yul.SoliditySpec
