import Solidity.Notation

/-! Keys (`Solidity/Test/Fixtures/Keys.sol`): mapping keys of every kind.  Harness input only. -/

namespace Keys.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def keys : SourceUnit := sol% contract Keys {
  enum Color { Red, Green, Blue }
  type Id is uint64;

  mapping(string => uint256) public byName;
  mapping(bytes => bool) public seen;
  mapping(string => mapping(bytes => uint256)) public nested;
  mapping(Color => uint256) public byColor;
  mapping(Id => uint256) public byId;
  mapping(Keys => uint256) public byContract;
  mapping(bytes4 => uint256) public bySel;
  mapping(int256 => uint256) public byInt;
  mapping(bool => uint256) public byBool;
  mapping(uint8 => uint256) public byU8;
  string public name;
  bytes public blob;

  function setByName(string memory k, uint256 v) external { byName[k] = v; }
  function setByNameCd(string calldata k, uint256 v) external { byName[k] = v; }
  function setLit(uint256 v) external { byName["alice"] = v; }
  function setFromStorage(uint256 v) external { byName[name] = v; }
  function setName(string memory n) external { name = n; }
  function getByName(string memory k) external view returns (uint256) { return byName[k]; }
  function getLit() external view returns (uint256) { return byName["alice"]; }
  function sumKeys(string memory a, string memory b) external view returns (uint256) { return byName[a] + byName[b]; }
  function del(string memory k) external { delete byName[k]; }
  function bump(string memory k) external returns (uint256) { byName[k] += 1; return byName[k]; }
  function emptyKeys() external view returns (uint256, bool) { return (byName[""], seen[""]); }
  function longKey(uint256 v) external { byName["a very long key that does not fit in thirty-two bytes"] = v; }
  function concatKey(string memory a, string memory b, uint256 v) external { byName[string.concat(a, b)] = v; }

  function mark(bytes memory k) external { seen[k] = true; }
  function markCd(bytes calldata k) external { seen[k] = !seen[k]; }
  function markBlob() external { seen[blob] = true; }
  function setBlob(bytes memory b) external { blob = b; }
  function markHex() external { seen[hex"deadbeef"] = true; }

  function setNested(string memory a, bytes memory b, uint256 v) external { nested[a][b] = v; }
  function getNested(string memory a, bytes memory b) external view returns (uint256) { return nested[a][b]; }

  function setColor(Color c, uint256 v) external { byColor[c] = v; }
  function setId(Id i, uint256 v) external { byId[i] = v; }
  function setContract(Keys c, uint256 v) external { byContract[c] = v; }
  function setSelf(uint256 v) external { byContract[this] = v; }
  function setSel(bytes4 s, uint256 v) external { bySel[s] = v; }
  function setInt(int256 i, uint256 v) external { byInt[i] = v; }
  function setBool(bool b, uint256 v) external { byBool[b] = v; }
  function setU8(uint8 x, uint256 v) external { byU8[x] = v; }
}

def program : Program := [keys]

end Keys.SoliditySpec
