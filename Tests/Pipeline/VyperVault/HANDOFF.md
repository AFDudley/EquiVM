# VyperVault — hand-off from the scaffolding session

Validation run of `Misc/scaffold-prompt.md` on a Vyper contract written for it
(`contracts/VyperVault.vy`): a payable deposit with a fee, `send`-based withdrawals under
`@nonreentrant`, an immutable owner, public getters.

## Compiler settings and provenance

- Vyper 0.4.3+commit.bff19ea2, `# pragma optimize gas` (the default), EVM version shanghai
  (`VyperVault.build.json`); sources pinned in `sources.sha256`.
- Generated with `scripts/scaffold.py all --dir Tests/Pipeline/VyperVault --vyper vyper
  --main VyperVault.vy --contract VyperVault --evm-version shanghai --module
  Tests.Pipeline.VyperVault`, then `bytecode_report.py`, `vy2stele.py` (no holes),
  `proof_skeleton.py` (the full Vyper skeleton). `SpecSyntax.lean` is the translator's draft, unedited.

## Differential run

```
lake exe stele-difftest --only VyperVault --count 50
VyperVault: 725 cases: 725 agree (357 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
```

Coverage (seed 2026): every transition and the constructor reach success
(`withdraw` 6/55, `collectFees` 14/63, `deposit` 14/60; the rest ≥ 13/59). `DiffTarget.lean`
adds `standardCallees` and the words `10^18`, `1`.

## Spec versus source

Audited block by block against `VyperVault.report.md`; the spec follows the source everywhere.
The compiler's guards are:

- the `callvalue` check of every non-payable entry (the macro's payability guard; for
  entries with arguments the bytecode folds it into one `calldatasize < 0x24 || callvalue`
  test), the address and bool validation of the arguments (`shr 160`, `shr 1`: the Vyper
  calldata decode mode), and the overflow/underflow checks of every `+`, `-`, `*`
  (`as uint256`);
- the reentrancy lock (shanghai: storage slot 0, `2` while locked, `3` after): `withdraw`
  and `collectFees` check `lock != 2`, store `2`, run the body and store `3` before
  returning. The spec writes this protocol around an internal `<f>_body`, with
  `nonreentrant_lock` declared first so `vyperStorage!` puts it at slot 0.
- `send(to, amount)` is `CALL` with gas 0 (the EVM stipend applies), value `amount`, no data,
  asserted: the spec's `(bool ok, bytes memory d) = to.call{value: amount}(new bytes(0));
  require(ok);`.
- `available` reads `balances[account]` then `SELFBALANCE` (the report shows it as
  `UNSUPPORTED_47`) and computes a branchless `min`; the spec binds the two reads in that
  order.

Dispatcher: a computed jump table, `selector % 11`, 2-byte entries at code offset 1407;
bucket → entry pc `[1399, 1399, 1399, 671, 1399, 1371, 1343, 1270, 1181, 24, 972]`, each
entry block comparing its own selector and falling through a chain:

| selector | signature | bucket | entry pc | chain |
|---|---|---|---|---|
| 0xd0e30db0 | deposit() | 9 | 24 | 24 → 461 (collectFees) → 1399 |
| 0xc8796572 | collectFees() | 9 | 24 | as above |
| 0x2e1a7d4d | withdraw(uint256) | 3 | 671 | 671 → 1399 |
| 0x16c38b3c | setPaused(bool) | 10 | 972 | 972 → 1153 (paused) → 1399 |
| 0x5c975abb | paused() | 10 | 972 | as above |
| 0x8da5cb5b | owner() | 8 | 1181 | 1181 → 1211 (balances) → 1399 |
| 0x27e235e3 | balances(address) | 8 | 1181 | as above |
| 0x10098ad5 | available(address) | 7 | 1270 | 1270 → 1399 |
| 0x7d882097 | totalDeposits() | 6 | 1343 | 1343 → 1399 |
| 0xf071db5a | feesCollected() | 5 | 1371 | 1371 → 1399 |

pc 1399 is the no-match revert (no `__default__`), pc 1403 the short-calldata/callvalue
revert. Constructor (creation pcs 0–31): callvalue guard, `OWNER = caller` written to the
immutable suffix, `CODECOPY`/`RETURN` of runtime ++ suffix.

Storage reads and writes are full words in the layout's slot order (`balances` 1,
`totalDeposits` 2, `feesCollected` 3, `paused` 4; mapping entries at
`keccak(slot ++ key)`), each one matched by a spec statement in the same order.

### Block coverage (`VyperVault.report.md`, runtime pcs; the constructor from the creation code)

Every block of the runtime is listed once; "guard revert" is pc 1403 (short calldata or
callvalue), "no match" pc 1399. Revert-payload blocks (the `assert` message encoding) belong to
the `require` they serve.

| function | blocks (pc) | spec statements, in order |
|---|---|---|
| dispatcher | 0–23 table lookup; 24, 461, 671, 972, 1153, 1181, 1211, 1270, 1343, 1371 compares; 1399; 1403 | `dispatchMsg` (`Dispatch.lean`) |
| `deposit` | 36–43 | `require(!paused)` (SLOAD 4) |
| | 44–164 | its payload (revert "paused") |
| | 165–170, 171–291 | `require(msg.value > 0)`, payload |
| | 292–306 | `(msg.value * 25) as uint256` (MUL + overflow check) |
| | 307–329 | `/ 10000`; `(msg.value - fee) as uint256` (underflow check) |
| | 330–361 | `balances[msg.sender] + credited` (KECCAK 1++caller, SLOAD, overflow check) |
| | 362–384 | SSTORE `balances`; `totalDeposits + credited` (SLOAD 2, check) |
| | 385–407 | SSTORE `totalDeposits`; `feesCollected + fee` (SLOAD 3, check) |
| | 408–460 | SSTORE `feesCollected`; `emit Deposited`; STOP |
| `collectFees` | 473–477 | `require(msg.value == 0)` (macro guard) |
| | 478–486 | `require(nonreentrant_lock != 2)` (SLOAD 0) |
| | 487–506 | `nonreentrant_lock = 2`; `require(msg.sender == OWNER)` (CODECOPY of the immutable) |
| | 507–627 | payload "not owner" |
| | 628–661 | `amount = feesCollected`; `feesCollected = 0`; `__a0.call{value: amount}`; `require(ok)` |
| | 662–670 | `nonreentrant_lock = 3`; `return amount` |
| `withdraw` | 683–692 | guard (`calldatasize < 0x24 || callvalue`) |
| | 693–701, 702–727 | lock check; `nonreentrant_lock = 2`; `require(balances[msg.sender] >= amount)` |
| | 728–848 | payload "insufficient" |
| | 849–876 | `(balances[msg.sender] - amount) as uint256` |
| | 877–899 | SSTORE; `(totalDeposits - amount) as uint256` |
| | 900–921 | SSTORE; `msg.sender.call{value: amount}`; `require(ok)` |
| | 922–971 | `emit Withdrawn`; `nonreentrant_lock = 3`; STOP |
| `setPaused` | 984–993, 994–1004 | guard; bool validation (decode mode) |
| | 1005–1023, 1024–1144 | `require(msg.sender == OWNER)`, payload |
| | 1145–1152 | `paused = flag`; STOP |
| `paused` | 1165–1169, 1170–1180 | guard; `return paused` |
| `owner` | 1193–1197, 1198–1210 | guard; `return OWNER` |
| `balances` | 1223–1232, 1233–1243 | guard; address validation |
| | 1244–1269 | `return balances[arg0]` |
| `available` | 1282–1291, 1292–1302 | guard; address validation |
| | 1303–1342 | `balances[account]`, `address(this).balance`, branchless `min`, return |
| `totalDeposits` | 1355–1359, 1360–1370 | guard; return |
| `feesCollected` | 1383–1387, 1388–1398 | guard; return |
| constructor | creation 0–9 | `require(msg.value == 0)` (macro guard) |
| | 10–31 | `OWNER = msg.sender` (CALLER into the suffix), CODECOPY/RETURN of runtime ++ suffix |
| | 32–35 | the guard's revert |

Findings: none. Every SLOAD/SSTORE above has its spec read or write in the same order
(mapping slots `keccak(slot ++ key)` through the Vyper backend); every revert is a `require`.

## Blockers

None.

## Proof status

Everything is proved: `lake build Tests.Pipeline.VyperVault.Correct` has no `sorry`; the
capstone `vyperVaultContractCorrect : contractRefinementWF storageWF noGasBound config
vyperVaultCreationBytecode contract` packages `vyperVaultConstructorCorrect` (the immutable
`OWNER` from `msg.sender`, `Constructor.lean`) with the runtime refinement `vyperVaultCorrect`
(one `…Body` theorem per selector).

- **Precondition** (`storageWF`, `Helpers.lean`): the `paused` word (slot 4) is `0` or `1`.
  Vyper returns and compares raw storage words, so the spec's `bool` view of the slot is the
  bytecode's word only for those two values; `setPaused` is the only writer and stores a
  validated calldata word, so the precondition is preserved.  The runtime theorem is therefore
  `runtimeRefinementWithWF storageWF noGasBound …`; the `…Body` theorems take
  `(hwf : storageWF σ I)` (the generator emits this shape with `proof_skeleton.py --wf storageWF`).
- Immutable `OWNER`: `deployed_of_fit` (`Common.lean`), `owner_of_fit`, `wordsOf_OWNER`,
  `suffixWords_OWNER`, `evalImmutable_OWNER` (`Helpers.lean`); the runtime is read with the
  generated `immWords` block summaries.
- The two `send`s are bridged with `callBridge` / `lowLevelCallSource` (`Reasoning/ExternalCall.lean`)
  over a `SourceState` chain of the storage writes before the call; the non-reentrant lock
  values `2`/`3` are compared as words.
- Shared Vyper lemmas added for these proofs live in `Reasoning/VyperDispatch.lean` (word
  arithmetic, memory reads around 32-byte writes, Vyper scalar storage views) and
  `Reasoning/VyperBounded.lean`.
- Gas bound: `noGasBound`; nothing in the body depends on the gas left.
