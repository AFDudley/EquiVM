# VyperRegistry — hand-off from the scaffolding session

Validation run of `Misc/scaffold-prompt.md` on a Vyper contract written for it
(`contracts/Registry.vy` with the module `contracts/lib/ownable.vy`): `initializes`/`exports`
of a module, a default argument (two selectors for `register`), a `DynArray` state with
`append`/`pop`, a struct mapping with a public getter, a loop over the array, events.

## Compiler settings and provenance

- Vyper 0.4.3+commit.bff19ea2, `# pragma optimize gas` (the default), EVM version cancun
  (`Registry.build.json`); sources pinned in `sources.sha256`.
- Generated with `scripts/scaffold.py all --dir Tests/Pipeline/VyperRegistry --vyper vyper
  --main Registry.vy --contract Registry --evm-version cancun --module
  Tests.Pipeline.VyperRegistry`, then `bytecode_report.py`, `vy2stele.py` (no holes),
  `proof_skeleton.py` (the full Vyper skeleton).
- Hand edits: `SpecSyntax.lean` adds `require(__n0 <= 16)` in `active_weight` (the compiler's
  loop bound, below); `Spec.lean` replaces `vyperStorage!` with `vyperBoundedStorage!` over
  explicit `VyperStorageDecl`s (`ids` has capacity 16 = `MAX_ENTRIES`).

## Differential run

```
lake exe stele-difftest --only Registry --count 50
Registry: 825 cases: 825 agree (363 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
```

Coverage (seed 2026): every transition and the constructor reach success; `deactivate`
1/61 and `pop_last` 7/59 need an owner caller and an active entry or a nonempty array in the
pre-state. `DiffTarget.lean` adds `standardCallees` and the words `1, 2, 3, 10^18`.

## Spec versus source

Audited block by block against `Registry.report.md`; the spec follows the source, with the
module's state and functions prefixed by the module alias (`ownable_owner`,
`ownable__check_owner`, `ownable___init__`). Compiler guards in the bytecode and their
statements:

- the `calldatasize`/`callvalue` test and address validation of every entry (decode mode and
  payability guard), the overflow/underflow checks of `+`/`-` (`as uint256`);
- `ids.append(id)`: the capacity check `len < 16` before the write (the backend's growth
  check on `push`, on the raw length word);
- `ids(i)`: `i < len` (the backend's index check); `pop_last`: `len > 0` (the source assert,
  plus the backend's own check on `pop`);
- `active_weight`: the loop is `repeat` with bound 16 and the compiler asserts `len <= 16`
  before it; the spec states it as `require(__n0 <= 16)` after reading the length once
  (the loop then reads `ids[i]` from storage at every iteration, as the bytecode does).
- `self.ids.pop()` only decrements the length word; the popped slot keeps its value. The
  Vyper backend's `pop` has the same semantics (`Stele/VyperStorage.lean`).

Dispatcher: a computed jump table, `selector % 10`, 2-byte entries at code offset 1665;
bucket → entry pc `[1533, 1123, 704, 1367, 24, 391, 1423, 764, 1486, 1533]`:

| selector | signature | bucket | entry pc | chain |
|---|---|---|---|---|
| 0xf0350c04 | transfer_ownership(address) | 4 | 24 | 24 → 256 (active_weight) → 1533 |
| 0x27a37ae6 | active_weight() | 4 | 24 | as above |
| 0x8da5cb5b | owner() | 5 | 391 | 391 → 418 (pop_last) → 1533 |
| 0xeffdfd55 | pop_last() | 5 | 391 | as above |
| 0x4420e486 | register(address) | 2 | 704 | 704 → 736 (nextId) → 1533 |
| 0x61b8ce8c | nextId() | 2 | 704 | as above |
| 0x6d705ebb | register(address,uint256) | 7 | 764 | 764 → 1533 |
| 0x916b9bef | deactivate(uint256) | 1 | 1123 | 1123 → 1533 |
| 0x06661abd | count() | 3 | 1367 | 1367 → 1395 (totalWeight) → 1533 |
| 0x96c82e57 | totalWeight() | 3 | 1367 | as above |
| 0xb30906d4 | entries(uint256) | 6 | 1423 | 1423 → 1533 |
| 0xfac333ac | ids(uint256) | 8 | 1486 | 1486 → 1533 |

pc 1533 is the no-match revert, 1661 the guard revert, 1537–1659 the internal routine
`ownable._check_owner` (slot 0 vs caller, revert "not owner"). Both `register` selectors
share the body from pc 793 after binding `weight` (the literal 1, or calldata word 2).
Constructor (creation pcs 0–34): callvalue guard, `ownable.__init__` as an internal routine
(`SSTORE 0 ← caller`), `nextId = 1` (`SSTORE 19`), `CODECOPY`/`RETURN`.

Storage: `ownable_owner` 0, `entries` 1 (struct fields at `keccak(1 ++ id) + 0/1/2`), `ids`
length 2 and data 3–18, `nextId` 19, `totalWeight` 20 — the layout `vyperBoundedStorage!`
derives from the declaration order.

### Block coverage (`Registry.report.md`, runtime pcs; the constructor from the creation code)

Every block of the runtime is listed once; "guard revert" is pc 1661, "no match" pc 1533,
`ownable._check_owner` is the internal routine 1537–1658 (SLOAD 0 vs caller, payload
"not owner") returning through 1659. Revert-payload blocks belong to the `require` they serve.

| function | blocks (pc) | spec statements, in order |
|---|---|---|
| dispatcher | 0–23 table lookup; 24, 256, 391, 418, 704, 736, 764, 1123, 1367, 1395, 1423, 1486 compares; 1533; 1661 | `dispatchMsg` |
| `transfer_ownership` | 36–45, 46–56 | guard; address validation |
| | 57–67, 1537–1659 | `ownable__check_owner()` |
| | 68–76, 77–195 | `require(new_owner != address(0))`, payload "zero owner" |
| | 196–255 | `previous = ownable_owner`; `ownable_owner = new_owner`; `emit OwnershipTransferred`; STOP |
| `active_weight` | 268–272 | `require(msg.value == 0)` |
| | 273–288 | `__n0 = ids.length`; `require(__n0 <= 16)` (the `repeat` bound) |
| | 289–295, 372–382 | loop entry and `__i0++ < __n0` |
| | 296–330 | `id = ids[__i0]`; `entries[id].active` (SLOAD 3+i, KECCAK, SLOAD +2) |
| | 331–364, 365–371 | `(total + entries[id].weight) as uint256`; `total =` |
| | 383–390 | `return total` |
| `owner` | 403–407, 408–417 | guard; `return ownable_owner` |
| `pop_last` | 430–434, 435–441 | guard; `ownable__check_owner()` |
| | 442–449, 450–568 | `require(ids.length > 0)`, payload "empty" |
| | 569–623 | `id = ids[ids.length - 1]`; `ids.pop()` (length word only); `entries[id].active` |
| | 624–658, 659–665 | `(totalWeight - entries[id].weight) as uint256`; SSTORE |
| | 666–703 | `entries[id] = Entry({…zero…})` (three SSTOREs); `return id` |
| `register(address)` | 716–725, 726–735 | guard; `weight = 1`, jump to the shared body |
| `register(address,uint256)` | 776–785, 786–792 | guard (0x44); `weight` from calldata word 2 |
| shared body | 793–804, 805–815 | address validation; `ownable__check_owner()` |
| | 816–824, 825–943 | `require(weight > 0)`, payload "zero weight" |
| | 944–966 | `id = nextId`; `(id + 1) as uint256` |
| | 967–1020 | SSTORE `nextId`; `entries[id] = Entry({…})` (three SSTOREs); `ids.push` capacity check (`len < 16`) |
| | 1021–1054 | SSTORE `ids[len]`, SSTORE length; `(totalWeight + weight) as uint256` |
| | 1055–1122 | SSTORE `totalWeight`; `emit Registered`; `return id` |
| `nextId` | 748–752, 753–763 | guard; return |
| `deactivate` | 1135–1144, 1145–1151 | guard; `ownable__check_owner()` |
| | 1152–1199, 1200–1318 | `entry = entries[id]` (three SLOADs); `require(entry.active)`, payload "inactive" |
| | 1319–1358, 1359–1366 | `entries[id].active = false`; `(totalWeight - entry.weight) as uint256`; SSTORE; STOP |
| `count` | 1379–1383, 1384–1394 | guard; `return ids.length` |
| `totalWeight` | 1407–1411, 1412–1422 | guard; return |
| `entries` | 1435–1444, 1445–1485 | guard; `return (account, weight, active)` (three SLOADs) |
| `ids` | 1498–1507, 1508–1520, 1521–1532 | guard; `arg0 < ids.length`; `return ids[arg0]` |
| constructor | creation 0–4 | `require(msg.value == 0)` |
| | 5–11, 35–39 | `ownable___init__()`: `ownable_owner = msg.sender` (SSTORE 0) |
| | 12–34 | `nextId = 1` (SSTORE 19); CODECOPY/RETURN |
| | 40–43 | the guard's revert |

Findings: none.

## Blockers

None.

## Proof status

Everything is proved: `lake build Tests.Pipeline.VyperRegistry.Correct` has no `sorry`; the
capstone `registryContractCorrect : contractRefinementWF storageWF noGasBound config
registryCreationBytecode contract` packages `registryConstructorCorrect` (`ownable.__init__`
as an internal call, `nextId := 1`, `Constructor.lean`) with the runtime refinement
`registryCorrect` (one `…Body` theorem per selector, including the `register` variants sharing
`registerTail` and the `active_weight` loop).

- **Precondition** (`storageWF`, `Helpers.lean`), under which the spec's typed view of the
  scalar storage is the bytecode's raw words:
  - the owner word (slot 0) is a canonical address (`owner()` returns the raw word; the owner
    check compares words);
  - every `entries[id]` holds a canonical account word and an `active` word in `{0, 1}`
    (`entries(uint256)` returns the raw words; `deactivate` tests the raw `active` word).
  Every writer stores validated words (`register` validates the address calldata word and
  stores `1` for `active`, `deactivate` stores `0`, `pop_last` stores zeros), so the
  precondition is preserved.
- **No array clause and no hash non-collision clause.** The Vyper backend reads the `ids`
  length word raw (`Stele/VyperStorage.lean`, `vyperLength?`), exactly as the bytecode does:
  `len(self.ids)` returns it, indexing checks `i < len`, `append` reverts on `len ≥ 16`, `pop`
  reverts on `len = 0`, and the `for` loop's compiler bound (`require(__n0 <= 16)` in the spec,
  pc 273 in the bytecode) reverts on a longer array.  `register` re-reads the length after the
  entry stores on both sides, so the entry slots may even alias slot 2 without affecting the
  refinement.
- `active_weight`: the loop is `awLoop` (`Active_weight.lean`), an induction on the remaining
  iterations that couples the EVM blocks 296→331→365→372 with Stele's `ExecForLoop` under the
  memory invariant `Minv` (`total` at offset 64).
- Shared Vyper lemmas for bounded storage (`DynArray` length, indexing, push, pop, struct
  reads/writes) are in `Reasoning/VyperBounded.lean`; word/memory helpers in
  `Reasoning/VyperDispatch.lean`.
- Gas bound: `noGasBound`.
