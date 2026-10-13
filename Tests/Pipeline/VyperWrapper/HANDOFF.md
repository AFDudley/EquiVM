# VyperWrapper — hand-off from the scaffolding session

Validation run of `Misc/scaffold-prompt.md` on a Vyper contract written for it
(`contracts/Wrapper.vy`): typed `extcall`/`staticcall` to an ERC20 interface held in an
immutable, a call without return data to an optional hook (Vyper's `EXTCODESIZE` guard),
checked arithmetic with division, public getters, events.

## Compiler settings and provenance

- Vyper 0.4.3+commit.bff19ea2, `# pragma optimize gas` (the default), EVM version cancun
  (`Wrapper.build.json`); sources pinned in `sources.sha256`.
- Generated with `scripts/scaffold.py all --dir Tests/Pipeline/VyperWrapper --vyper vyper
  --main Wrapper.vy --contract Wrapper --evm-version cancun --module
  Tests.Pipeline.VyperWrapper`, then `bytecode_report.py`, `vy2solm.py` (no holes),
  `proof_skeleton.py` (the full Vyper skeleton). `SpecSyntax.lean` and `Spec.lean` are the generated files,
  unedited.
- `DiffTarget.lean` is edited: the `TOKEN` immutable is fixed to the standard callee `0x5000`
  (every call answered with the word 1) instead of a generated constructor run, so that `wrap`
  and `unwrap` reach their success paths.

## Differential run

```
lake exe solm-difftest --only Wrapper --count 50
Wrapper: 625 cases: 625 agree (319 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
```

Coverage (seed 2026): every transition and the constructor reach success (`unwrap` 10/64,
`wrap` 12/59, `setHook` 13/64, the rest ≥ 47/68).

## Spec versus source

Audited block by block against `Wrapper.report.md`; the spec follows the source everywhere.
Compiler guards and call conventions in the bytecode:

- the `calldatasize`/`callvalue` test and address validation of every entry, the
  overflow checks of `*` and `+`, the underflow checks of `-`, and the division-by-zero
  checks (`as uint256`, and Solm's `/` reverting on zero). In `wrap` the bytecode checks the
  multiplication, then the subtraction, then the zero divisor, which is the spec's evaluation
  order of `((amount * totalShares) as uint256) / ((held - amount) as uint256)`.
- `extcall IERC20(TOKEN).transferFrom/transfer(...)` is `CALL` with all gas, 32-byte output
  buffer; failure bubbles the return data as a revert; then `returndatasize >= 32` and a
  bool validation (`shr 1`). The spec binds `bool ok = __aN.transferFrom(...)` with the
  immutable receiver hoisted into an address local; the `externalABI` of `Spec.lean` decodes
  the bool in modern mode (the same `returndatasize` and 0/1 checks).
- `staticcall IERC20(TOKEN).balanceOf(self)` is `STATICCALL` with the same checks;
  `{view}` in the spec.
- `extcall IHook(self.hook).onWrap(...)` returns nothing: the bytecode asserts
  `EXTCODESIZE(hook) != 0` before the `CALL` (the spec's `require(hook.code.length > 0)`),
  no return-data check after it.
- The bytecode reads `hook` once for the `!= 0` test and once more for the call target; the
  spec reads the slot three times (test, guard, receiver), all of the same word.

Dispatcher: a computed jump table, `selector & 7`, 2-byte entries at code offset 1764;
bucket → entry pc `[213, 1728, 1639, 24, 1756, 1756, 897, 1756]`:

| selector | signature | bucket | entry pc | chain |
|---|---|---|---|---|
| 0xea598cb0 | wrap(uint256) | 0 | 213 | 213 → 1756 |
| 0x3a98ef39 | totalShares() | 1 | 1728 | 1728 → 1756 |
| 0xfc0c546a | token() | 2 | 1639 | 1639 → 1669 (shares) → 1756 |
| 0xce7c2ac2 | shares(address) | 2 | 1639 | as above |
| 0x3dfd3873 | setHook(address) | 3 | 24 | 24 → 186 (hook) → 1756 |
| 0x7f5a7c7b | hook() | 3 | 24 | as above |
| 0xaa9b074e | previewUnwrap(uint256) | 6 | 897 | 897 → 1486 (previewUnwrap)… |
| 0xde0e9a3e | unwrap(uint256) | 6 | 897 | 897 (unwrap) → 1486 → 1756 |

pc 1756 is the no-match revert, 1760 the guard revert. Constructor (creation pcs 0–53):
callvalue guard, the `token` argument copied from the end of the initcode and
address-validated (`shr 160`), written to the immutable suffix, `CODECOPY`/`RETURN`.

Storage: `hook` 0, `shares` 1 (`keccak(1 ++ owner)`), `totalShares` 2; the immutable `TOKEN`
in the 32-byte code suffix (`Immutables.lean`).

### Block coverage (`Wrapper.report.md`, runtime pcs; the constructor from the creation code)

Every block of the runtime is listed once; "guard revert" is pc 1760, "no match" pc 1756.
"bubble" blocks copy the callee's return data and revert with it: the external call's failure
case of the Solm `externalCall`. Revert-payload blocks belong to the `require` they serve.

| function | blocks (pc) | spec statements, in order |
|---|---|---|
| dispatcher | 0–23 table lookup; 24, 186, 213, 897, 1486, 1639, 1669, 1728 compares; 1756; 1760 | `dispatchMsg` |
| `setHook` | 36–45, 46–56 | guard; address validation |
| | 57–66, 67–178 | `require(hook == address(0))`, payload "hook set" |
| | 179–185 | `hook = target`; STOP |
| `hook` | 198–202, 203–212 | guard; return |
| `wrap` | 225–234 | guard |
| | 235–241, 242–353 | `require(amount > 0)`, payload "zero" |
| | 354–401, 402–408 | `__a0 = TOKEN`; `ok = __a0.transferFrom(msg.sender, address(this), amount)`; failure bubbles |
| | 409–431, 432–442 | `returndatasize >= 32`, bool validation (the `externalABI` decode) |
| | 443–461, 462–573 | `require(ok)`, payload "transfer failed" |
| | 574–616, 617–623 | `minted = amount`; `held = __a2.balanceOf{view}(address(this))`; bubble |
| | 624–632 | `returndatasize >= 32` (decode) |
| | 633–648, 649–659, 660–667 | `totalShares > 0 && held > amount` (short-circuit) |
| | 668–689 | `(amount * totalShares) as uint256` |
| | 690–709, 710–719 | `(held - amount) as uint256`; divisor `!= 0` (Solm `/`) |
| | 720–729 | `minted =` |
| | 730–757, 758–780 | `(shares[msg.sender] + minted) as uint256`; SSTORE; `(totalShares + minted) as uint256` |
| | 781–794 | SSTORE; `hook != address(0)` |
| | 795–821 | `require(hook.code.length > 0)` |
| | 822–836, 837–843, 844–845 | `__c2 = hook.onWrap(msg.sender, minted)`; bubble; join |
| | 846–896 | `emit Wrapped`; `return minted` |
| `unwrap` | 909–918 | guard |
| | 919–940, 941–1052 | `require(shares[msg.sender] >= sharesOut)`, payload "insufficient" |
| | 1053–1089, 1090–1096, 1097–1105 | `held = __a0.balanceOf{view}(address(this))`; bubble; decode |
| | 1106–1135 | `(sharesOut * held) as uint256` |
| | 1136–1148, 1149–1185 | `totalShares != 0`; `/`; `(shares[msg.sender] - sharesOut) as uint256` |
| | 1186–1208, 1209–1258 | SSTORE; `(totalShares - sharesOut) as uint256`; SSTORE; `ok = __a2.transfer(msg.sender, amount)` |
| | 1259–1265, 1266–1288, 1289–1299 | bubble; decode (`returndatasize`, bool) |
| | 1300–1320, 1321–1434 | `require(ok)`, payload "transfer failed" |
| | 1435–1485 | `emit Unwrapped`; `return amount` |
| `previewUnwrap` | 1498–1507 | guard |
| | 1508–1514, 1515–1526 | `if (totalShares == 0) return 0` |
| | 1527–1563, 1564–1570, 1571–1579 | `held = __a0.balanceOf{view}(…)`; bubble; decode |
| | 1580–1609, 1610–1622, 1623–1638 | `(sharesOut * held) as uint256`; `totalShares != 0`; `/`; return |
| `token` | 1651–1655, 1656–1668 | guard; `return TOKEN` (CODECOPY) |
| `shares` | 1681–1690, 1691–1701, 1702–1727 | guard; address validation; return |
| `totalShares` | 1740–1744, 1745–1755 | guard; return |
| constructor | creation 0–9 | `require(msg.value == 0)` |
| | 10–26 | the `token` argument copied from the end of the initcode, address-validated (decode) |
| | 27–53 | `TOKEN = token` into the suffix; CODECOPY/RETURN |
| | 54–57 | the guard's revert |

Findings: none. The `GAS` before every call is the forwarded gas the relation leaves to the
oracle; nothing else reads it.

## Blockers

None.

## Proof status

Everything is proved: `lake build Tests.Pipeline.VyperWrapper.Correct` has no `sorry`; the
capstone `wrapperContractCorrect : contractRefinementWF storageWF noGasBound config
wrapperCreationBytecode contract` packages `wrapperConstructorCorrect` (the `token` argument
decoded from the initcode tail into the immutable `TOKEN`, `Constructor.lean`) with the runtime
refinement `wrapperCorrect` (one `…Body` theorem per selector).

- **Precondition** (`storageWF`, `Helpers.lean`), under which the spec's `address` view of
  `hook` is the bytecode's raw word:
  - the `hook` word (slot 0) is a canonical address (`hook()` returns the raw word; `setHook`
    and `wrap` compare it with zero as a word);
  - hash non-collision: the caller's `shares` slot is not slot 0 (`wrap` stores
    `shares[msg.sender]` before it re-reads `hook`);
  - `hookStableAcrossCalls σ I`: every message call made from this contract's account map `σ`
    leaves slot 0 a canonical address word.  `wrap` re-reads `hook` after
    `TOKEN.transferFrom(...)`, whose callee is opaque to the proof (it is bridged to the EVM
    `Θ`), and a re-entrant callee could in principle store any word; the contract's own
    `setHook` only stores validated words, which this clause records for arbitrary callees.
    It is stated over `Ethereum.EVM.Θ` with this contract as the sender and quantifies over the
    callee, calldata, gas and substate.
  `setHook` validates the calldata word, so the first clause is preserved.
- External calls: `Reasoning/VyperCalls.lean` bridges Vyper's `CALL` (value 0) and `STATICCALL`
  to Solm's `typedCallViaEVM` (`typedCallBridge`, `typedStaticCallBridge`, via `callCoincides`),
  evaluates the modern-mode return decoders (`decodeReturn_*`), Vyper's `returndatasize` check
  (`rdsCheck_*`) and its multiplication check (`mulCheck_*`).  `CallHelpers.lean` computes the
  ABI encodings `externalABI.encode?` produces for the four interface calls and the call
  memory the bytecode builds (`tfMem`, `balMem`, `bal2Mem`, `trMem`, `callMem2`).
- Gas bound: `noGasBound`; the calls forward all gas (`GAS` before each call), which the
  relation leaves to the oracle.
