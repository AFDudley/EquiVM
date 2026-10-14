# MetaMorphoV1_1 proving handoff

## Completed proof — 2026-10-14

The constructor and all 76 runtime proofs are complete. There are no remaining
`sorry` or `admit` declarations, including hidden Lean scratch files. The older
progress notes below are historical; their outstanding-work lists are superseded.

The user-approved patch is applied: `metaMorphoV1_1ConstructorCorrect` proves
`typedConstructorRefinementWithCodeBound`, and `metaMorphoV1_1ContractCorrect`
proves `contractRefinementWFWithCodeBound trivialStorageWF noGasBound`. The added
constructor premise is `I.code.size < UInt256.size`. Runtime refinement retains
its existing unrestricted storage and gas conditions.

The final constructor work covers the approval probe, malformed return data,
empty returns and code-size checks, allocation failures, and the fallback
`approve(0)` followed by reuse of the original maximum-approval request.
`ConstructorForceApprove.lean` packages that source/EVM segment.
`ConstructorApproveSource.lean` and `ConstructorApproveInit.lean` connect it to
the final constructor statements, including `DECIMALS_OFFSET`.

The deployment tail copies 19708 bytes from creation offset 3894, then patches
all 32 immutable sites. `ConstructorRuntimeMemory.lean`, `ConstructorRuntimeParts.lean`,
and `ConstructorRuntime.lean` prove the three deployment blocks and exact returned
bytes. `SparseCopyMemory.lean` covers free pointers beyond currently written
memory; `RuntimeWriteWindow.lean` relocates the patches into the runtime window.
`ConstructorFinalImmutables.lean`, `ConstructorImmutableMemory.lean`, and
`ConstructorDeployedCode.lean` connect every memory word to the source immutable
store and prove its declared types fit. `ConstructorSuccess.lean` packages success.

Final verification:
- `lake build Benchmarks.Morpho.MetaMorphoV1_1.Correct` passed, 4632 jobs;
  see `.constructor-complete-build.log`.
- `.constructor-complete-axioms.lean` checks both completed constructor and contract
  theorems. Each depends only on `propext`, `Classical.choice`, `Quot.sound`, and
  concrete native evaluation axioms (8899 constructor / 31658 contract).
  See `.constructor-complete-axioms.log`; no custom axioms or `sorryAx` occur.
- Scoped searches found no Lean `sorry`, `admit`, or `axiom` declarations;
  `git diff --check` passed. Every authored proof file stays below 2000 lines;
  the pre-existing generated `Bytecode.lean` is the only larger Lean file.
- No differential tests or semantic audit were rerun. No generated block,
  bytecode artifact, pinned source, or unrelated working-directory file was edited.
- Changes are unstaged and uncommitted. No further proof work is pending.

## Compiler settings and provenance

The proof target is the **local solc 0.8.37 rebuild**, as authorized when the storage-array
compiler bug was identified. The original mainnet deployment uses solc 0.8.26. Its successful
byte-for-byte reproduction is retained separately; upgrading the compiler changes both the
executable bytecode and its metadata.

- Upstream: [morpho-org/metamorpho-v1.1](https://github.com/morpho-org/metamorpho-v1.1/tree/5a0717b2c863060ff452ca324716083fe6d09374),
  commit `5a0717b2c863060ff452ca324716083fe6d09374`, main unit `src/MetaMorphoV1_1.sol`.
  The pristine tree and dependency commits are in `../metamorpho-v1.1/UPSTREAM.json`.
- Ethereum factory: `0x1897A8997241C1cD4bD0698647e4EB7213535c24`, listed by
  [Morpho](https://docs.morpho.org/developers/contracts/addresses/).
  Its creation transaction is `0x4c19401df000d3bbc3fe364049c93913e0aa350e0cbb7d01dd9f27aaa2c512e9`
  at block `21439510`.
- Reference vault: [Steakhouse PAXG](https://etherscan.io/address/0xbeef7959ae71d4e45e1863dae0b94c35244af816?amt=1-10),
  `0xBeeF7959aE71D4e45e1863dae0B94C35244AF816`, chain ID `1`.
  `provenance/vault.address.json` records the factory as creator and creation transaction
  `0xe95cfc831c42977fa643013a694390700fffe43ca462d0fd585f36a113e3c85d`.
  Etherscan marks the contract as an exact verification match.
- Historical compiler: `0.8.26+commit.8a97fa7a`. The verification source closure and settings
  are retained in `provenance/verification.standard-input.json`; the explorer responses and
  Etherscan settings excerpt are retained alongside it. The excerpt is from another vault
  using this same template. The historical comparison independently checks all bytes of the
  selected PAXG vault, including the IPFS/CBOR metadata tail.
- Current compiler: `0.8.37+commit.f401782d`, official Linux amd64 binary SHA-256
  `5de843c2c93563cc66425c99a4fb13fdbf32b4c4ae07469480faaf126e14404a`.
  [Compiler manifest](provenance/benchmark-compiler.json) records the download URL and reason.
- Settings: optimizer enabled, `200` runs, `viaIR: true`, `evmVersion: cancun`,
  `metadata.bytecodeHash: ipfs`, `appendCBOR: true`, `useLiteralContent: false`.
  All nine verification remappings are preserved in the build manifest.
- `compiler-sources/` contains the same 41 compilation units. The sole source change is the
  main unit's exact pragma, `0.8.26` to `0.8.37`; pristine upstream files remain unchanged.
  ABI, storage layout, and immutable names/types are unchanged.

| Artifact | Runtime bytes | Equals reference deployment, metadata included |
| --- | ---: | --- |
| Saved 0.8.26 template with reference immutables | 19730 | Yes |
| Current 0.8.37 template with reference immutables | 19708 | No; intentional compiler upgrade |

The comparison records are `provenance/deployment-solc-0.8.26-comparison.json` and
`provenance/deployment-comparison.json`. Current creation bytecode is 23666 bytes.

Recompile and regenerate with the pinned binary:

```sh
python3 Benchmarks/Morpho/MetaMorphoV1_1/recompile.py --solc /path/to/solc-0.8.37
```

The fresh Morpho Blue callee is in `../MorphoBlue/`: upstream commit
`55d2d99304fb3fb930c688462ae2ccabb1d533ad`, solc `0.8.19+commit.7dd6d404`,
optimizer `999999` runs, via IR, Paris, IPFS metadata. Its 15623-byte patched runtime matches
the deployed Blue code. This is a callee fixture; the vault proof target uses 0.8.37.

## Differential tests and validation

All seven scaffold checks pass. The final Lean build completed successfully (3661 jobs).
The 17 correlated cases, all three packed-slot cases, and the three array-cleanup checks pass.
The randomized run results and per-transition coverage follow below.

```sh
python3 scripts/scaffold.py check --dir Benchmarks/Morpho/MetaMorphoV1_1
lake build Benchmarks.Morpho.MetaMorphoV1_1.Correct \
  Benchmarks.Morpho.MetaMorphoV1_1.DiffTarget \
  Benchmarks.Morpho.MetaMorphoV1_1.FixedBlue.DiffTarget
lake exe stele-difftest --only MetaMorphoV1_1 --count 50 --seed 2026
lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/DifferentialScenarios.lean
lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/ArrayCleanupRegression.lean
lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/PackedStorageRegression.lean
```

On this machine the native executable command uses
`LEAN_CC=/tmp/metamorpho-native-toolchain/bin/cc` before `lake exe`; that temporary wrapper
supplies the installed Lean clang with the available C headers and linker libraries.
No repository toolchain or shared generator was changed for that workaround.

Both registered targets have name `MetaMorphoV1_1`, so `--only` selects both. The first patches
`MORPHO` to real Blue at `0xBBBBBbbBBb9cC5e90e3b3Af64bdAF62C37EEFFCb`; the second patches it to
the fixed-response interface fixture at `0x6000`. Both install true-returning ERC20 bytecode
at the asset address and no-return ERC20 bytecode at `0x5001`. Their Yul sources and compiled
bytecode are retained in `fixtures/`. `marketWords` includes three IDs checked against
CreateMarket logs; full parameters are in `provenance/created-markets.json`.

Independent random state does not supply a coherent live Blue market. The correlated fixture
run explicitly covers two successful constructors, cap submission/acceptance, a nonempty
supply queue, positive deposit and withdrawal, redemption, retaining and removing a withdrawal
market, reallocation through both withdrawal and supply, market removal, skim with both ERC20
return conventions, and a valid timelock submission. These are vault-interface tests against the fixed Blue fixture, not
claims about a live lending market.

Successful `permit` is not covered: this machine's differential runner does not provide the
required working ecrecover precompile path. The spec models the STATICCALL to address `1`;
the proof must handle it. Random coverage gaps are explained with the final results below.


Actual seed-2026 output, in registry order:

**Real Blue**

```text
MetaMorphoV1_1: 4025 cases: 4025 agree (1813 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
  successful/cases: constructor 1/25, totalAssets() 28/51, name() 40/50, convertToAssets(uint256) 17/51, approve(address,uint256) 32/53, previewWithdraw(uint256) 23/52, revokePendingCap(bytes32) 19/50, totalSupply() 45/51, revokePendingGuardian() 15/51, lostAssets() 49/54, transferFrom(address,address,uint256) 2/50, setSupplyQueue(bytes32[]) 18/50, setSkimRecipient(address) 12/51, decimals() 47/53, withdrawQueueLength() 41/51, DOMAIN_SEPARATOR() 44/51, skimRecipient() 44/51, asset() 46/50, MORPHO() 40/50, submitCap((address,address,address,address,uint256),uint256) 0/51, maxDeposit(address) 43/50, updateWithdrawQueue(uint256[]) 6/52, guardian() 43/50, feeRecipient() 44/53, revokePendingMarketRemoval(bytes32) 18/52, previewRedeem(uint256) 20/52, isAllocator(address) 40/51, lastTotalAssets() 49/54, withdrawQueue(uint256) 7/54, setFee(uint256) 3/54, deposit(uint256,address) 0/53, acceptCap((address,address,address,address,uint256)) 0/53, balanceOf(address) 36/51, renounceOwnership() 9/52, submitTimelock(uint256) 0/50, reallocate(((address,address,address,address,uint256),uint256)[]) 10/50, pendingGuardian() 44/52, acceptOwnership() 8/51, pendingTimelock() 46/50, nonces(address) 34/50, submitMarketRemoval((address,address,address,address,uint256)) 0/51, eip712Domain() 47/51, acceptTimelock() 21/50, owner() 41/51, mint(uint256,address) 0/51, symbol() 48/51, submitGuardian(address) 1/52, supplyQueueLength() 40/52, pendingCap(bytes32) 42/50, acceptGuardian() 18/50, transfer(address,uint256) 11/52, multicall(bytes[]) 16/52, DECIMALS_OFFSET() 42/50, setIsAllocator(address,bool) 4/51, previewMint(uint256) 24/50, withdraw(uint256,address,address) 0/53, setSymbol(string) 13/51, redeem(uint256,address,address) 0/50, skim(address) 4/52, setName(string) 14/52, maxMint(address) 20/50, convertToShares(uint256) 20/50, revokePendingTimelock() 21/51, config(bytes32) 39/51, maxWithdraw(address) 8/52, timelock() 47/51, permit(address,address,uint256,uint256,uint8,bytes32,bytes32) 0/50, maxRedeem(address) 7/52, allowance(address,address) 40/52, fee() 47/51, pendingOwner() 48/53, curator() 47/53, setFeeRecipient(address) 6/51, setCurator(address) 12/51, previewDeposit(uint256) 27/54, transferOwnership(address) 7/50, supplyQueue(uint256) 8/51, stray 0/100
```

**Fixed Blue**

```text
MetaMorphoV1_1: 4025 cases: 4025 agree (1834 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
  successful/cases: constructor 1/25, totalAssets() 27/51, name() 40/50, convertToAssets(uint256) 15/51, approve(address,uint256) 32/53, previewWithdraw(uint256) 26/52, revokePendingCap(bytes32) 19/50, totalSupply() 45/51, revokePendingGuardian() 15/51, lostAssets() 49/54, transferFrom(address,address,uint256) 2/50, setSupplyQueue(bytes32[]) 18/50, setSkimRecipient(address) 12/51, decimals() 47/53, withdrawQueueLength() 41/51, DOMAIN_SEPARATOR() 44/51, skimRecipient() 44/51, asset() 46/50, MORPHO() 40/50, submitCap((address,address,address,address,uint256),uint256) 0/51, maxDeposit(address) 43/50, updateWithdrawQueue(uint256[]) 3/52, guardian() 43/50, feeRecipient() 44/53, revokePendingMarketRemoval(bytes32) 18/52, previewRedeem(uint256) 16/52, isAllocator(address) 40/51, lastTotalAssets() 49/54, withdrawQueue(uint256) 7/54, setFee(uint256) 3/54, deposit(uint256,address) 2/53, acceptCap((address,address,address,address,uint256)) 0/53, balanceOf(address) 36/51, renounceOwnership() 9/52, submitTimelock(uint256) 0/50, reallocate(((address,address,address,address,uint256),uint256)[]) 10/50, pendingGuardian() 44/52, acceptOwnership() 8/51, pendingTimelock() 46/50, nonces(address) 34/50, submitMarketRemoval((address,address,address,address,uint256)) 0/51, eip712Domain() 47/51, acceptTimelock() 21/50, owner() 41/51, mint(uint256,address) 2/51, symbol() 48/51, submitGuardian(address) 1/52, supplyQueueLength() 40/52, pendingCap(bytes32) 42/50, acceptGuardian() 18/50, transfer(address,uint256) 11/52, multicall(bytes[]) 16/52, DECIMALS_OFFSET() 42/50, setIsAllocator(address,bool) 4/51, previewMint(uint256) 21/50, withdraw(uint256,address,address) 4/53, setSymbol(string) 13/51, redeem(uint256,address,address) 0/50, skim(address) 4/52, setName(string) 14/52, maxMint(address) 20/50, convertToShares(uint256) 19/50, revokePendingTimelock() 21/51, config(bytes32) 39/51, maxWithdraw(address) 25/52, timelock() 47/51, permit(address,address,uint256,uint256,uint8,bytes32,bytes32) 0/50, maxRedeem(address) 17/52, allowance(address,address) 40/52, fee() 47/51, pendingOwner() 48/53, curator() 47/53, setFeeRecipient(address) 5/51, setCurator(address) 12/51, previewDeposit(uint256) 25/54, transferOwnership(address) 7/50, supplyQueue(uint256) 8/51, stray 0/100
```

Zero-success entries in the random run are intentional coverage limits, not disagreements:

- `submitCap`, `acceptCap` and `submitMarketRemoval` need matching market IDs and coherent
  configuration/pending values. All three have successful correlated scenarios.
- Real Blue's random world lacks initialized market state for deposit/mint/withdraw/redeem.
  Fixed Blue supplies successful deposit, mint and withdrawal samples; the correlated sequence
  also exercises a positive withdrawal and a redemption.
- `redeem` had no successful random sample under either target: its balance, share conversion
  and withdrawal-liquidity conditions were not jointly met. The correlated redemption covers it.
- `submitTimelock` needs an authorized owner, no pending update, a different current value,
  and a new value in `[86400, 1209600]`. The correlated submission covers the valid combination
  this seed did not reach.
- `permit` has no successful sample for the ecrecover limitation above. `stray` is deliberately
  malformed or unknown-selector calldata, so zero successful calls is expected.

The executable also prints diagnostics for unavailable BN_ADD/BN_MUL/SNARKV foreign
precompiles during initialization. These are not vault-test disagreements; the vault scenarios
above do not use those precompiles.

## Where the spec follows compiled behavior

The semantic audit covers all 76 selector arms, shared runtime routines, constructor code,
and rejection of unknown/short calldata. There is no receive or fallback function. The later
proof-valuation issue below was resolved with approved bounds. The remaining function and
constructor proofs are still in progress.

- `PendingAddress` includes an explicit `uint32 padding` field. Solidity packs its declared
  address and uint64 into 224 bits, but deletion clears the entire slot. Ordinary field
  updates preserve the upper 32 bits. Minimal regression: owner calls
  `revokePendingGuardian()` with `storage[15] = 2^224`; bytecode and corrected spec both leave
  zero. The regression also covers `submitGuardian`'s immediate branch and `acceptGuardian`.
- Role helpers preserve the compiler's short-circuit read order. Pending-value updates cache
  the timelock before their first field write. `_setCap` caches `lastTotalAssets` before its
  external view calls, and `skim` caches its recipient before `balanceOf`.
- `_withdrawable` checks supply-minus-borrow underflow before calling the token's `balanceOf`.
  Checked arithmetic, narrowing checks, array allocation/growth limits, enum validation,
  short-string length checks and compiler calldata guards are explicit or supplied by the
  standard ABI/storage semantics.
- The ID hash is the hash of five ABI words. `supplyShares` and `lastUpdate` use Blue's
  `extSloads` interface with the library's exact slot derivation. The source convenience
  methods are not separate external calls in the bytecode.
- OpenZeppelin `mulDiv` uses an exact mathematical product with a checked quotient, preserving
  full-precision behavior; Morpho's multiplication helpers instead check the intermediate
  256-bit product. Rounding and division-by-zero checks remain distinct.
- SafeERC20 models low-level calls, optional Boolean returns, code-existence checks and
  failure propagation. Supply/withdraw try-catch catches callee failure; malformed return
  data after a successful call still reverts. Multicall uses self-DELEGATECALL. Revert payloads
  are abstracted by the framework, while success returns and events remain part of comparison.

The original compiler issue is
[LostStorageArrayWriteOnSlotOverflow](https://www.soliditylang.org/blog/2025/12/18/lost-storage-array-write-on-slot-overflow-bug/),
fixed in solc 0.8.32. For a short counterexample, set
`B = uint256(keccak256(abi.encode(uint256(20))))`, `storage[20] = 2^256 - B`, and
`storage[B] = 7`, then call `setSupplyQueue([])` as owner. The old runtime succeeds while
leaving `7`; 0.8.37 enters cleanup and exhausts finite gas. Ordinary two-element cleanup also
passes the regression. The enormous length is an artificial raw-storage case. No storage
backend changes or slot-noncollision axioms were introduced.

## Guidance for the proving session

Start from `Correct.lean`. The original skeleton had 78 placeholders: 76 function bodies,
the constructor, and `Common.restrictImmutables_of_fit`. Handwritten proofs now replace the
bridge and twenty-nine function stubs. Do not force-regenerate the skeleton:
that would overwrite this proof work. `SpecSyntax.lean` remains authoritative.

`Dispatch.lean` now imports five source-dispatch shards and five EVM-reach shards. Every shard
is below 2,000 lines; original theorem statements and proofs are retained. `BodyCommon.lean`
contains shared source guards, byte-length arithmetic, selector exclusion, and return encoding.

There are **eleven** immutables, including inherited OpenZeppelin fields. The test valuation
is `deployedImmutables` in `DiffTarget.lean`; values and current offsets are also in
`provenance/deployment-comparison.json`.

| Immutable | Reference valuation |
| --- | --- |
| `_asset` | `0x45804880de22913dafe09f4980848ece6ecbaf78` |
| `_underlyingDecimals` | `18` |
| `_cachedDomainSeparator` | `0x8f37e0b6d6c1781e97de5ecb3bae2dd56076e9111d4b253739015ae80df19392` |
| `_cachedChainId` | `1` |
| `_cachedThis` | `0xBeeF7959aE71D4e45e1863dae0B94C35244AF816` |
| `_hashedName` | `keccak256("") = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470` |
| `_hashedVersion` | `keccak256("1") = 0xc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6` |
| `_name` | `0` (empty ShortString) |
| `_version` | `0x3100000000000000000000000000000000000000000000000000000000000001` |
| `MORPHO` | `0xBBBBBbbBBb9cC5e90e3b3Af64bdAF62C37EEFFCb` |
| `DECIMALS_OFFSET` | `0` |

The theorem is parameterized over fitting immutable valuations; it is not restricted to the
test valuation. Use current `Immutables.lean` offsets, never the historical offsets.

`external-abi.lean.inc` supplies the manual boundary encodings: five-word MarketParams,
six uint128 Market fields, Position's uint256/uint128/uint128, two separate uint256 results
for `supply` and `withdraw`, dynamic bytes32 arrays for `extSloads`, and the ERC20/IRM calls.
It converts named memory structs to ABI tuples and converts decoded structs back. The actual
runtime uses `extSloads` for positions; the `position` entry documents the complete interface.

Expect the queue loops, cap enablement/removal, reallocation, fee/loss accounting, full-precision
mulDiv, SafeERC20 call paths, multicall, EIP712/permit and constructor immutables to need most
work. Reason over raw packed slots and cached reads; preserve storage effects around calls.
View-call preservation can justify cached queue lengths. Array cleanup must account for
finite gas on enormous raw lengths; the overflow regression's out-of-gas result is not a
successful equivalence test. Begin with the simple getters and shared arithmetic/call helpers.

`MetaMorphoV1_1.report.md` is the runtime block/source report. A full creation disassembly can
be generated with `python3 scripts/bytecode_report.py Benchmarks/Morpho/MetaMorphoV1_1
--full-creation --output /tmp/metamorpho-full-report.md`. Executable init code ends at PC 3893;
the embedded runtime starts at byte 3894, followed by the two constructor event-topic constants.

Earlier detailed progress through transfer is preserved in
[HANDOFF_HISTORY_2026_10_14.md](HANDOFF_HISTORY_2026_10_14.md).

## Delegated transfer completed

`TransferFrom` is proved, leaving 31 original placeholders. Focused build passed
(`/tmp/metamorpho-public-transfer-from-build.log`, 3630 jobs), and LSP is clean. No model changes
or added assumptions. The final one-line wrap in TransferFromBodySource followed the build;
include it in the next dependency build.

All allowance helpers are now built: AllowanceInternalSource, SpendAllowanceSource, Calls,
Lookup, Guards, Store, Static, Function. Lookup computes the nested slot and branches on
`allowed + 1`; allowanceAddOne_ne_zero proves the finite case. Static stops at SSTORE 12646.
`spendAllowanceFunctionReturn/Revert/Static` use a source State's executionEnv/accountMap,
bound R+11, and return the exact `spendAllowanceState` accounts. Return requires permission
only for a finite allowance. Unlimited allowances work under static calls.

New TransferFunction proves return/revert/static of the full internal transfer over an arbitrary
source state, bound R+10. TransferFromEntry proves both address decoders and 100-byte calldata
guard; use generic `solcDecodeLenCheckOk/Short/Huge` for width96 (no `_4_96` library aliases).
TransferFromBodySource threads source allowance state into the balance reads. Public theorem
also preserves the dispatcher's selector stack tail; it is not an empty stack.

The only pending work is the remaining original placeholders. Next active group:
RevokePendingTimelock (entry2053, selector61) and RevokePendingGuardian (entry10526, selector7).
Both use `_checkGuardianRole`, delete their pending packed record, and emit caller.
AccessControl only contains owner-role helpers; find/prove guardian-role helpers before these.


## Pending-change revocations completed

All four public revocations now have complete proofs. LSP diagnostics are clean and focused
builds passed. Original placeholder count is now 27. No spec/model changes in this group.

- `GuardianRoleSource.lean`: source function 10 `_checkGuardianRole`, owner or guardian.
- `PackedDeletion.lean`: generic byte-field clear word, adjacent clears, overwrite, missing-account
  handling, and full-slot deletion of pendingTimelock (slot17) and pendingGuardian (slot15,
  including its existing uint32 padding). No added storage assumptions.
- `RevocationSource.lean`: Bool-selected (true=guardian) source bodies, success/revert/static.
- `RevocationRole.lean`: owner comparison then optional guardian check. Timelock PCs
  2070→2090/2152→2095; guardian PCs10543→10563/10610→10568; sharedrevert2137.
- `RevocationEntry.lean`: nonpay/length guards, store-return, first SSTORE static at2098/10571.
- `RevokePendingTimelock.lean`, `RevokePendingGuardian.lean`: complete public proofs.
  `/tmp/metamorpho-public-revocation-build.log` passed3527jobs.
  Public signatures were subsequently wrapped only for width; format rebuild queued separately.
- `CuratorGuardianSource.lean`: function9 `_checkCuratorOrGuardianRole` source proof.
  Source OR parses right-associatively: guardian OR (curator OR owner).
- `MarketRevocationMutation.lean`: delete pendingCap[id] slotmapping16 entirely;
  delete config[id].removableAt slotmapping13 preserving low192bits.
- `MarketRevocationSource.lean`: Bool-selected (true=cap) source bodies with bytes32 id.
- `MarketRevocationRole.lean`: runtime authorization shared between cap and market-removal:
  market PCs7757guardian→7891curator→7779ownerchoice→7870owner→7785require→7790store;
  cap PCs10678guardian→10784curator→10700ownerchoice→10763owner→10706require→10711store.
  Both use sharedrevert7855. Guardian comparison masks on right, unlike other comparisons.
- `MarketRevocationStore.lean`: exact slot hashing, storage/event/return, and static at
  7815 (market-removal) /10724 (cap). Prefixes copied only from provided summaries.
- `MarketRevocationEntry.lean`: entries7739/10660, length checks7745/10666, bytes32 decoding.
  First build missed Decode import, then fixed and LSP clean; final public build covers fix.
- `RevokePendingCap.lean`, `RevokePendingMarketRemoval.lean`: complete public proofs.
  `/tmp/metamorpho-public-market-revocation-build.log` passed3542jobs.
- All intermediate helper focus builds passed. `git diff --check` passed.
- `TransferFrom` formatting rebuild from previous handoff passed3630jobs.

Next active group: AcceptTimelock (entry4895, selector41), AcceptGuardian(entry4172,selector48).
No edits to these yet. Internal `_setTimelock` stores timelock, msgSender/event, then deletes
pendingTimelock. `_setGuardian` stores packed guardian, msgSender/event, deletes pendingGuardian.
Each public acceptance reads pending validAt, requires nonzero and timestamp≥validAt, then calls
its setter on pending value. Start by proving these internal setters. Source atSpecSyntax187,
212, publicacceptances1322/1385. Read summaries before choosing any runtime PCs.

## Timelock and guardian acceptance completed

`AcceptTimelock` and `AcceptGuardian` are proved; 25 original placeholders remain.
Joint focused build passed3619jobs: `/tmp/metamorpho-public-accept-pending-build.log`.
LSP clean, new files fit100columns, no model/spec changes or assumptions.
Previous revocation-format build also confirmed passed3527jobs.

- SetTimelockSource (function2) and SetGuardianSource (function5) prove internal setter
  success/static/calls. Timelock stores14, event, clears17; guardian updates packed12,
  event, clears15. SetPendingRoutines proves bytecode14755/15404 return/static. Static
  SSTORE PCs14759/15435. Return boundsR+5/R+7; timelock changes memory atfreepointer,
  guardian preservesmemory.
- AcceptPendingSyntax defines packed read, time/value, sourcebody/frame, sourceguardprefix.
  Booltrue=guardian. Time uses UInt256.ofNat(timestamp), matching EVM wrapping.
- AcceptPendingSource proves success/static and missing/premature reverts.
- AcceptPendingEntry proves nonpay/lengthguard at4895/4901 (timelock) or4172/4178 (guardian).
- AcceptPendingGuards: read4912/4189, nonzerotime→4925/4211, timepassed→4931/4217;
  missing→4249, premature→4234. Source-state based bridges, boundR+4.
- AcceptPendingRoutines: valuejump4931/4217→setter14755/15404, sharedreturn1867STOP.
  pendingGuardianValueWord converts maskedvalue to canonicaladdress word.
  StoreReturn/Static boundR+7, exactacceptPendingState accounts.
- All intermediate focus builds passed (source,entry,guards,routines).

Current active function: SubmitGuardian, entry4368 selector45. Original placeholder untouched.
Internal setterdone. Need prove pendingGuardian value+validAt writes, owner+guards,
zero-currentguardian immediate setter versus deferredpendingrecord path, static and reverts.
Source SpecSyntax1357; runtime blocks024/025. No edits for this function yet.

## Guardian submission completed

`SubmitGuardian` is proved; 24 original placeholders remain. Focused public build passed3630jobs
(`/tmp/metamorpho-public-submit-guardian-build.log`), LSP clean. No model/spec changes.
All helper builds passed except the first ScheduledGuardianStatic standalone build, which had
an .olean file-not-found race with LSP/dependency work; subsequent SubmitGuardianRoutines and
public builds succeeded and cover it. Do not rerun differential suite or audit.

- PendingTimeStorage: uint64 at offset20 (pendingGuardian.validAt), arithmetic word, exact
  bytecode mask/shift equivalence, source storageLocStore. UInt256.shiftLeft must unfold with
  explicit if_neg, then Fin.shiftLeft_val; direct `change` can time out on the Fin comparison.
  Nat.land/lor wrapper names and Nat.and/or operator names sometimes need explicit `change`.
- PendingGuardianMutation: low64 cast, source assignments of address and time, states, snapshot
  of timelock and checked timestamp+timelock bound. Scheduled state preserves padding/high32bits.
- SubmitGuardianSyntax: fixed decoded locals, adminFrame, guards, scheduled frame and AST.
  The actual elaborated `as uint256` time sum is `.inRange`, not `.cast`: overflow is modeled
  correctly in existing SpecSyntax, no repair needed. Checked addition occurs after value write.
- ScheduledGuardianSource: deferred update success, overflow revert, staticfirstwrite.
- SubmitGuardianSource: complete source success/static/guardrevert/overflowrevert.
- SubmitGuardianEntry:4368nonpay→4374length32→4386decoder11163→4393owner12917→4401.
- SubmitGuardianGuards:4401unchangedguard→4426pendingtimeguard→4445branch;
  unchangedrevert1143, pendingrevert4572. BoundR+6; output[currentword,newword,newword]R.
  solcAddrMask_clean_left needs explicit `(w := UInt256.ofNat value.val)` to avoid EVM.word
  vsUInt256.ofNat rw failures.
- ScheduledGuardianRoutines:4458 writes15value→12077checkedadd→4491timewrite/event/STOP.
  BoundR+7. `scheduledGuardianReachAdd` retains old timelock snapshot. Same update state threaded
  through overflow path. ScheduledGuardianStatic firstSSTORE4485,prefixfromprovidedsummary.
- SubmitGuardianRoutines:4445→4449→15404 immediate setter (return1867) or4458scheduled.
  StoreReturn/Static/RevertOverflow share exact source state; boundR+7.
- `git diff --check` passed, new files fit100columns after two wraps before public build.

Current active: SubmitTimelock, entry6869 selector33. Original placeholder untouched.
New TimelockBoundsSource proves function1 `_checkTimelockBounds`, source calls and reverts;
LSP clean, not yet built. Upper1209600,lower86400.
Runtime (blocks035/036):6869nonpay→6875length32→6887loadword+owner12917return6897.
6897new≠old14guard→6908pending17high64zero→6918upperbound→6928lowerbound→6938branch.
Upperrevert7088,lower7073,unchanged1143,pending4572.
6938new>old→6946→14755setterreturn1867; else6955 writespending17low192value (mask184),
then12077checkedtimestamp+oldtimelock return7029. 6955 stack afterwrite:
[timestamp,oldtimelock,7029,new,32,eventTopic]R; eventTopic definedinprovidedsummary.
7029takes[time,new,32,eventTopic]R, updateshigh64of17 preservinglow192, emits andstops,boundR+9.
Need prove pendingTimelock uint192 value + uint64 time storage first; valid new value bound means
uint184 cast is identity. Read summaries for staticfirstwritePC and eventtopic; do not guess.

## Timelock submission completed

`SubmitTimelock` is proved; 23 original placeholders remain. Focused public build passed
(`/tmp/metamorpho-public-submit-timelock-build.log`), LSP clean, `git diff --check` passed.
No model/spec changes. Do not rerun the differential suite or audit.

- TimelockBoundsSource: function1 `_checkTimelockBounds`, upper1209600/lower86400,
  source call success and revert. Build passed3494jobs.
- PendingTimelockStorage: low192 value and high64 timestamp packed updates, exact bytecode
  mask/shift identities, storageLocStore proofs. For pendingTimeHighShift, unfold shiftLeft,
  Fin.shiftLeft_val, Nat.shiftLeft_eq, then change only the modulo divisor with conv_lhs;
  globally rewriting UInt256.size breaks the dependent Fin type of data.val.
- PendingTimelockMutation: source assignments, state after each store, checked time snapshot.
- SubmitTimelockSyntax: decoded/admin/post-bounds frames; different/noPending/increase guards;
  prefix includes `_checkTimelockBounds`. Source value cast184 is identity under bounds.
  For Int comparison simplification use Int.ofNat_eq_natCast and Nat.cast_lt, not Int.ofNat_lt.
- ScheduledTimelockSource and SubmitTimelockSource: all success, static, guard, overflow paths.
- SubmitTimelockEntry:6869→6875length32→6887loadword/owner12917return6897; badlength/nonpay.
- SubmitTimelockGuards:6897different→6908pendingtimezero→6918upper→6928lower→6938branch;
  reverts1143/4572/7088/7073. BoundR+4.
- ScheduledTimelockRoutines:6955 low192 store masked184 (bounded value makes masks equal),
  checked addition12077→7029 high64 store/event/STOP. BoundR+9. Exact source state match.
- ScheduledTimelockStatic: first SSTORE6982, prefix copied from generated summary throughr20.
- SubmitTimelockRoutines:6938→6946→14755setter/1867STOP or6955deferred, all outcomes.
  StoreReturn/RevertOverflow take timelockInBounds; source hgood supplies it.
- All helper builds passed, public build3635jobs passed; new files fit100 characters.

Current active: SetIsAllocator selector52 entry3552. Original placeholder untouched.
SpecSyntax1420: nonpayable, calldata bound, `_checkOwner`,
require(isAllocator[newAllocator] != newIsAllocator), assign bool mapping, emit.
Need inspect decoder/runtime summaries and reuse MappingStorage/IsAllocator/Decode helpers.

## Allocator setter completed

`SetIsAllocator` is proved; 22 original placeholders remain. Focused public build3531jobs passed
(`/tmp/metamorpho-public-set-is-allocator-build.log`), all helper builds passed, LSP clean,
new files fit100characters, git diff --check passed. No model/spec changes.

- AllocatorMutation: slot11 address mapping, low-byte boolean read/normalized word,
  state preserving upper31bytes, generic source read/assignment. boolWordNeSource compares
  arbitrary stored bool bytes by normalized words. Avoid broad simp with `w.val=0 ↔ w=0`:
  it loops. Use simp only to rewrite wordToElem, then split zero cases and decide.
- SetAllocatorSource: decoded/admin frames, unchanged guard, source success/static/revert.
  Parameters are semantic address and raw UInt256 flag, canonical flag0∨1 for guard.
- SetAllocatorEntry:3552nonpay→3558length64→3570addressdecoder11163ret3577,
  3577boolcanonicalcheck→3592owner12917ret3599. Bad flag and length/nonpay reverts.
  Reuse boolWordClean_iff and u256_sub_eq_zero_iff_eq.
- SetAllocatorGuards:3599 computes addressmapping11 in scratchmem, reads/normalizes bool,
  unchanged→1143, different→3637[flag,addr]R, mem twoWordHashMem addr11solcFreePtrMem.
  Rewriting raw generated storage/hash expression by folded helper failed; rewrite the
  source-side condition backwards with allocatorBoolWord_bytecode, then `exact` matches.
- SetAllocatorRoutines:3637write/event/STOP, maskflag255=normalizedflag for canonical values,
  exact setAllocatorState match. twoWordHashMem_solcMappingSlot_any needs no memory bound.
- SetAllocatorStatic: prefix3637throughr22, firstSSTORE3696. BoundR+8.

Current active: SetFeeRecipient selector71 entry1158. Original placeholder untouched.
SpecSyntax1582: owner, new!=old feeRecipient, !(new=0 && fee!=0), `_accrueInterest`,
assignfeeRecipient,event. Prove dependency `_accrueInterest` first (SpecSyntax194).
No work yet beyond reading this path; inspect existing accrued-fee simulation and token mint proofs.

## Fee-recipient setter completed

`SetFeeRecipient` is proved; 21 original placeholders remain. Public build 3760 jobs passed
(`/tmp/metamorpho-public-set-fee-recipient-build.log`); public LSP clean, new files fit 100
characters, git diff --check passed. Original public theorem API/docstring preserved.

Authorized/reported cursor correction: new `AccrueInterestAllocationSyntax` appends
`allocatedAccrueInterestFunction` (index105), wrapping allocated fee/assets calculation and
returning its cursor, and replaces transition71's accrual call with cursor128. Spec imports it;
Common.setFeeRecipientSelectorOf unfolds allocatedSetFeeRecipientTransition. Existing original
function3 remains unchanged. Other mutating transitions need the same correction when active.

Completed dependencies:
- UpdateLastAssetsSource: function47 store22 + event; generic source call/return/static.
- UpdateLastAssetsRoutines:16830 store/event/return, first static SSTORE16870. R+6.
- MintSupplySource: mint branch of function73 `_update`, checked slot2 supply increment,
  then recipient balance read/store (after supply write), then Transfer. All source outcomes.
- MintInternalSource: function48 `_mint`, nonzero recipient + `_update`, all call outcomes.
- MintRoutines:17718 recipientguard→17735 load supply→12077 checkedadd→17783 ordered stores
  and Transfer/return. R+10. No storage-slot noncollision assumption. Static SSTORE17786.
- AccrueInterestSource/TailSource: allocated calculation, tuple unpacking, lastTotalAssets
  store22 then lostAssets store23/events, optional mint, event + cursor return.
- AccrueInterestRoutines:14262→12247 ret14340, then16830 ret14353, loss store and branch to
  14369 directevent or14382→17718 mint ret14397→14369. Named work stacks/memory.
- AccrueInterestSimulation: all runtime/source outcomes, R+40, SourceState preserved through
  writes and actual external-call state. Success includes I.perm=true, frame/state/cursor,
  mem/out/RD; does NOT assert memory cursor preservation after event writes.
- FeeRecipientMutation: high-address (offset12,size20) packed storage, low96 bits preserved.
- SetFeeRecipientSource/Entry/Guards/Routines: complete public composition. Guard1317 consumes
  an additional stack item (selector); pass w::tag::R, not arbitrary empty R.

Proof engineering: `rw [← hs.env] at rd` can also rewrite the initial state and calldata words
in a public trace; use `nth_rw 1 [← hs.env] at rd` when only the current execution env should
change. This fixed an elaborator timeout; public theorem needs default heartbeats.
`addressOfNat_eq_iff_solcAddrMask_eq` puts the mask on the LEFT. Use solcAddrMask_clean_left.
For bytecode packed stores, instantiate source helper's slot as UInt256.ofNat18 and unfold
codeOwnerStorageWord before rw: matching against literal⟨18⟩ inside storage getD can fail.

Current active: SetFee selector28 entry7417, original placeholder untouched. Shares the now
completed interest-accrual dependency. No work yet beyond reading its public placeholder;
inspect transition28 and runtime path, then extend the authorized cursor correction to it.

### Fee setter completed

`SetFee.lean` now has its original public theorem proved with default heartbeats and
maxRecDepth 2000. Public build passed (3763 jobs):
`/tmp/metamorpho-public-set-fee-build.log`. **20 original placeholders remain.**

The authorized cursor correction extends `AccrueInterestAllocationSyntax.lean` with
`allocatedSetFeeTransition`, replacing transition 28's body index 7 call with
`__solcAccrueInterest(128)`. `Spec.lean` replaces transition 28 and
`Common.setFeeSelectorOf` unfolds the correction. Dependency build passed 3738 jobs,
and all setter leaves plus Dispatch passed 3762 jobs. No new assumptions or sorries.

New helpers: `FeeMutation.lean` (low96 store, preserving upper160), `SetFeeEntry.lean`
(nonpay/calldata/owner), `SetFeeGuards.lean` (same fee, cap, recipient checks),
`SetFeeSource.lean` (all source paths), `SetFeeRoutines.lean` (7511 store+event+STOP).
Entry 7417→7423→7435→12917(return7445), equality→7465, cap→7480,
recipient checks→7489→7495→14262(return7511, value, mask96, selector).
Source `setFeeAllowed` is different fee ∧ value≤5e17 ∧ ¬(nonzero fee ∧ zero recipient).
After accruing, the fee store reads the **post-accrual** slot18, as bytecode does.

Proof detail: `setFeeState.executionEnv` is propositionally preserved by
`storageStore_executionEnv`, not definitionally. Explicitly rewrite it after
`msgSenderCall` before equating the final frame. Otherwise `change`/unification unfolds
contract and times out. Type the final fee-read fact with the exact final frame for simp.
Public source environment rewrite uses `nth_rw 1 [← hs'.env]` to avoid rewriting I
inside the initial state and calldata stack words. Width≤100 for new files; diff check clean.

Current active next function: `Name.lean` selector1 entry10884; original placeholder
still untouched. Source simply returns storage `_vaultName`. `Symbol.lean` analogous
selector44 entry4587. No string helper work yet. Do not rerun differential tests or audit.

### Name getter completed; shared string machinery

`Name.lean` now has its original public theorem proved with default heartbeats and
maxRecDepth 2000. Focused public build passed (3551 jobs):
`/tmp/metamorpho-public-name-build.log`. **19 original placeholders remain.**

Reported and applied the authorized cursor correction to both metadata getters:
`StringViewAllocationSyntax.lean` adds a local string read followed by
`__solcAllocate(128, bytes.size + 32)` and return. `Spec.lean` replaces transitions 1
and 44, and `Common.lean` selector proofs unfold those replacements. The bytecode copies
the storage string, then the allocator enforces the 64-bit cursor limit; the original
source getter omitted that panic branch. No extra assumptions or shared semantics edits.

String helpers (all checked/built): `StringHeader.lean` and `StringHeaderRoutines.lean`
decode valid headers and reject malformed ones at 11801. `StringStorageSource.lean`
proves the source payload and its size. `StringViewSource.lean` proves all source
outcomes. `StringAllocation.lean` relates the rounded copy size and source allocation.
`StringCopyLoop.lean` proves arbitrary-length copying with storage-slot wraparound;
`StringCopyMemory.lean` defines short/long memory layouts and the short header mask.
`StringMemoryRead.lean` proves payload reads and length-word preservation.
`StringReturnMemory.lean` proves generic ABI header + MCOPY + trailing-zero encoding.
`StringReturnRoutines.lean` composes 2379→11086→4335 into the shared encoder.
`StringAllocatedReturn.lean` composes allocation and return for any storage base slot.
`NameEntry.lean` and `NameCopyRoutines.lean` cover the name-specific entry/copy path.

Name path: 10884(nonpay)→10890(length guard)→10901→11801(return10916), then short
4753 or long 10932→10955→10999(loop11023)→11007; both reach4643→11329 allocator
return2379→11086→4335. Data at160, length128, copied end160+32*ceil(len/32).
Both empty strings and enormous strings that fail allocation are covered.

Active next: Symbol selector44 entry4587. Runtime path has corresponding
4587→4593→4604→11801(return4619), short4753 or long4635→4659→4703(loop4727)→4711.
It then uses the same allocator and encoder. Current plan is to generalize the loop
and copy routing across the two bytecode instances, preserving one induction proof.

### Symbol getter completed and common string proof factored

Both public getters now build together (3555 jobs), with default heartbeats:
`/tmp/metamorpho-public-string-getters-build.log`. **18 original placeholders remain.**
The original public statements/docstrings remain intact. No new model changes since
the already reported shared string allocation correction.

`NameEntry.lean` became `StringEntry.lean`, parametrized by `symbol : Bool`.
`NameCopyRoutines.lean` became `StringCopyRoutines.lean`; its public helper is
`stringCopyToAllocation v symbol`. Added `StringCopyBlocks.lean` for the two loop
instances and `StringCopySetup.lean` for short/long routing. `StringCopyLoop.lean`
now has one `stringCopyLoop v symbol` induction used by both getters.
All new string files are ≤100 columns and `git diff --check` passed.

A concurrent intermediate dependency build reported a missing StringCopyMemory.olean
during refactoring. The subsequent consolidated public build rebuilt all affected
dependencies and passed; do not treat the older failed log as a current proof error.

### DOMAIN_SEPARATOR completed

`DOMAIN_SEPARATOR.lean` now proves its original public theorem with default heartbeats
and maxRecDepth 2000. Both cache checks and the rebuilt five-word Keccak preimage are
covered, along with nonpayable/huge-calldata reverts. No specification correction was
needed: the public rebuild allocates 192 bytes from cursor128, which always fits.
**17 original placeholders remain.**

New helpers: `DomainHashSource.lean` (type hash, five words, functions45/build-domain),
`DomainSource.lean` (function38/cache selection and public source body),
`DomainMemory.lean` (preimage length/free/data), `DomainHashRoutines.lean`
(13028→11329→13174→return), `DomainCacheRoutines.lean`
(12937/address check→13180/chain check→12987→cached12993 or rebuild13028),
and `DomainEntry.lean` (9689→9695→9706→12937).
The internal runtime theorem accepts arbitrary free≥96 with free+192<2^64 and
preserves the exact conditional memory; it can be reused by Permit.
Public encoding reuses `maxDepositEncodeReturn` at1578.

Lean detail: `uInt256OfByteArray` is not definitionally `ofNat(fromByteArrayBigEndian)`;
rewrite with `uInt256OfByteArray_eq`. Normalize literal UInt256.toNat by `change`
after pointer arithmetic, so simp does not unfold the variable pointer too early.

Active next function: Eip712Domain selector40 entry4948. Its source calls
functions `_EIP712Name`, `_EIP712Version`, and `ShortStrings_toString` (the latter
checks low8 length≤31, returns the prefix). Fallback storage is used only when
_name/_version equals 255. Investigate full source and bytecode before implementation.

Focused public DOMAIN_SEPARATOR build passed (3549 jobs):
`/tmp/metamorpho-public-domain-separator-build.log`.

### Eip712Domain in progress (17 original placeholders still remain)

Reported and applied the authorized allocation correction: new
`Eip712AllocationSyntax.lean` preserves the original prefix/default declarations,
then allocates after each string read (64 bytes for an immutable short string;
32+string byte length for a storage fallback), and allocates32 for empty extensions.
`Spec.lean` replaces transition40; `Common.eip712DomainSelectorOf` unfolds it.
Dependencies passed 3536 jobs (`/tmp/metamorpho-eip712-allocation-deps-build.log`).
A consolidated shared build passed 3580 jobs, including ShortStringRoutines, Name,
Symbol, DOMAIN_SEPARATOR (`/tmp/metamorpho-eip712-shared-check-build.log`).
Public Eip712Domain theorem is still the original placeholder.

New checked helpers:
* `ShortStringSource.lean`: low8 length, validity≤31, prefix bytes; generic
  `evalExpr_wordAnd`; source function89 returns/reverts.
* `Eip712StringSource.lean`: functions39/_EIP712Name and40/_EIP712Version,
  immutable sentinel255 versus storage slots5/6, validity/bytes, source bodies and
  caller wrappers, payloadsize<2^255.
* `Eip712StringAllocationSource.lean`: selected allocation size and source returns/reverts.
* `ShortStringMemory.lean`: exact runtime memory (allocate64, initialize32, calldata
  exhausted copy, replace length, store word), length/free/payload/MemoryPrefix.
* `ShortStringRoutines.lean`: 18425/18521 short decoder→11329 allocator→18452→ret;
  malformed length→18471 revert. Built in the consolidated check above.
* `FallbackStringMemory.lean`: arbitrary-cursor storage-copy memory, padded coverage,
  length/data/free-pointer preservation, MemoryPrefix. Built.
* `FallbackStringSetup.lean`: 11857→11801 decoder; 11872 short→11957→ret;
  long11872→11888→11900→11914. Generic storage base Keccak lemma. Built.
* `FallbackStringCopy.lean`: complete11857 valid copy→ret/end cursor; invalid-header
  revert. Uses generalized shared loop induction. LSP clean and focused build started
  `/tmp/metamorpho-fallback-string-copy-build.log` (session57218).
* `StringBuffer.lean`: length/padded allocation/data predicate; MemoryPrefix.readWords
  and StringBuffer.preserve. LSP clean; build started
  `/tmp/metamorpho-string-buffer-build.log` (session3493).

Refactors: `StringStorageSource.stringStorageLayout` now public; added generic
`storageStringReadAt`/`storageStringReadAtReverts`, and existing metadata read theorems
wrap them. `StringCopyBlocks.lean` adds StorageStringLoopKind (metadata Bool/fallback),
pc/exit/stack selectors and generic step/exit summaries. `StringCopyLoop.lean` now
has ONE `storageStringCopyLoop` induction; original `stringCopyLoop v symbol` API
wraps the metadata case. Existing public name/symbol rebuilt successfully.

Important memory detail: MemoryPrefix preserves 32-byte windows starting≥96, so it
already tolerates allocator writes at64 and hash scratch at0. StringBuffer.preserve
extends it to arbitrary string payload lengths using padded allocation coverage.
`MemoryArrayData.lean` already has writeOutsideSource_size/read for calldata zero-fill;
reuse those. ByteArray.write beyond source does not extend destination itself, but the
following word writes do.

Remaining EIP work: compose fallback copy with18505→11329→11757→ret and domain
sentinel branches18416/18512. Assemble source transition (defaults + two calls and
allocations). Prove 7-component ABI encoding and runtime5068→11086→5104→11086→5118
→5158(fallthrough emptyarray)→5166 RETURN. Reuse StringReturnRoutines/Memory for shared
11086 encoder, probably generalize it to arbitrary source/destination and internal ret.
The public entry4948→4954→4965 calls18416 with[_name,5008,5104];5008 calls18512 with
[_version,5049] and saved name pointer. 5049 allocates32 for empty extensions, return5068.

### Eip712Domain completed; next Skim

The original public Eip712Domain theorem is now fully proved. Focused public build passed
3649 jobs (`/tmp/metamorpho-public-eip712-domain-build.log`). **16 placeholders remain.**
No further specification correction beyond the preceding allocation correction was needed.
Generic fallback and short string routines now return a `StringBuffer`, free pointer and
`MemoryPrefix`; `StringBuffer.preserve` reuses `HeapWordWindow.memoryPrefix_read_words`.
`StringEncoderMemory` and `StringEncoderRoutines` extract the shared payload encoder;
StringReturnMemory/Routines now wrap those, preserving their old APIs. Name and Symbol
rebuilt successfully. EIP helpers cover source defaults/calls/allocation/reverts, seven-value
ABI encoding, two string encoders, empty extensions, and final RETURN. New files are named
Eip712{SourcePrefix,Source,ABI,ReturnMemory,EncodeMemory,FinishRoutines,EncodeRoutines,
ExtensionsRoutines,Entry}, Eip712String{Memory,Routines}, FallbackString{Allocation,Routines}.
All helpers passed focused builds. Two final edits only wrapped long lines in
Eip712SourcePrefix and Eip712EncodeRoutines.

Next selected function: Skim (selector57, entry2710). Inspection only so far. It needs a
balanceOf STATICCALL at2795 and SafeERC20_safeTransfer at15818. Existing TokenBalanceCall
simulation is fixed to19570 and can be generalized. Source internal functions are in
SpecSyntax; no SafeERC20 proof helpers yet. Inspect transfer/raw-call allocation behavior
before deciding whether a source cursor correction is needed. Do not switch to another
public function because this dependency is difficult. No current confirmed new mismatch.

### Skim transfer dependency completed

Confirmed, reported, and applied the authorized allocation-accounting correction for Skim:
the raw token-call return buffer can panic before optional-return validation. New
SafeTransferAllocationSyntax defines cursor-aware Address/optional-return/safeTransfer helpers;
Spec appends them at function indices106–108 and replaces transition57. Existing function
indices are preserved. Skim passes cursor160 after balanceOf's fixed32-byte reservation.
SafeTransfer allocates100 rounded to128, then accounts for nonempty raw return data.

All dependency helpers are proved and focused builds passed: ZeroCallSimulation,
AddressVerifySource/Routines, CallReturnMemory/Allocation/Routines/Source,
AddressCallSource, OptionalReturnSource/Routines, OptionalCallSource/Simulation/Routines,
TwoWordCallMemory, SafeTransferABI/Source/Memory/Routines. The complete
`safeTransferSimulation` matches runtime15818→11329→15877→18967→CALL18992→15478
return allocation→18567 address validation→19007 optional Boolean→14753→caller.
It covers both parent permission modes, depth failure, request/return allocation failure,
call failure, empty data with code check, and canonical/noncanonical Boolean decoding.
Latest build passed3605jobs `/tmp/metamorpho-safe-transfer-routines-build.log`.

Skim public theorem remains the original placeholder (16 total remain). Next work is its
balance call, recipient guard, event/static halt, then public composition. Entry2710;
balance call setup2755→2795; after CALL2796 stack[ok,recipient,ptr,token]R. Success
2796→2803→2867→2882→11329 allocator→2895→2904[ptr,recipient,token]R
→2809[2821,recipient,balance,token]R→15818[token,recipient,balance,2821,balance,token]R.
Failure2796→2921. Short return via2867→2913→2882→allocator→2895→917.
At initialptr128 the successful allocation always fits, cursor160. Reuse TokenBalanceCall
ABI/request memory and TokenBalanceMemory postcall facts. Source balance statement is
externalCall(.var token) balanceOf0[.env this] amount false (inspect actual DSL lowering).
Use `tokenBalanceReturnSize` for size<2^255; `typedStaticcallSimulation` accepts arbitraryPC.
Recipient is low160bits slot19; Storage.evalStorage_skimRecipient exists. At2821 event succeeds
using generated block2821 when I.perm=true; for false step toLOG3pc2865 then RD.log3Static.
`msgSenderCall` is in ApprovalCalls and source `ExecStmt.emitStatic` handles the final halt.

Useful new transfer API: SafeTransferRoutines.safeTransferSimulation requires SourceState,
free pointer<2^64, pointer≥128, mem.size≥128, free64 and zero96 words. It returns either
source revert+RDrev, or evm'/cursor/mem'/out and SourceState, source function success,
and RD at caller ret. SafeTransferSource uses an abstract optional callee ExecFuncBody,
avoiding duplicate source proofs. Runtime routines use generic stack tails.

### Skim completed; next SetName

Skim's original public theorem is now fully proved, including nonpayable/short/huge/noncanonical
calldata, zero recipient, failed and short balance returns, all SafeERC20 paths, and final
LOG3 static halt. Focused public build passed3661jobs (`/tmp/metamorpho-public-skim-build.log`).
**15 original placeholders remain.** Added SkimSource, SkimBalanceRoutines, SkimBalanceMemory,
SkimEntry, SkimEvent, and SkimSimulation; all LSP-clean and built. Initial memory has size96;
SkimBalanceMemory proves that the balance request's first write at128 fills the zero slot,
then return copying and free-pointer update preserve it. SkimSimulation composes calls from
pc2755 through success/revert/static outcomes; Skim.lean handles dispatcher and ABI decoding.
No new correction beyond the previously recorded transfer allocator correction.

Next selected public function: SetName(string), entry2240, selector58. Original source is
nonpayable/calldata bound→_checkOwner→_vaultName=newName→emitSetName. SetSymbol shares the
string-storage writer. No setter helpers exist yet; current string helpers are reads/encoders.
Reasoning.Storage has bytes/string backend write lemmas (roughly lines1300–1505), and
Reasoning.StorageLoops may provide loop machinery. No newly confirmed mismatch.

### SetName decoder and storage loops

SetName remains selected; its public theorem is still the original placeholder (15 remain).
Confirmed and reported a missing initial string-allocation panic in the source model:
ABI decoding admits lengths near the 64-bit maximum, while the runtime allocator at11329
can fail before the owner check. Applied the previously authorized allocator correction to
both metadata setters in StringSetAllocationSyntax, with Spec overrides at58 and55. Their
source bodies now account for allocation from128 of32+length. No function indices changed.

Completed and built: CalldataBytesRoutines, StringCalldata, StringDecoderEntry,
CalldataBytesMemory, StringDecoder, StringStorageWrite, StringSetSource, StringStorageHash,
StringClearLoop, StringBufferWords, and StringDataLoop. The shared decoder11698 covers
malformed heads/offsets/lengths, allocation panic, payload bounds, and successful StringBuffer
construction. StringSetSource covers allocation/owner/header reverts, assignment static halt,
and successful assignment plus event. StringStorageWrite exposes exact source storage order.
StringClearLoop proves both setters' old-data clearing loops. StringDataLoop proves full-word
stores directly against solidityDataWordsForwardFrom; latest build passed3604jobs in
/tmp/metamorpho-string-data-loop-build.log. StringCopySetup now reuses the extracted slot hash
facts instead of its identical inline native_decide proofs. No new assumptions/placeholders.

Next: mask/partial-word lemmas, clearing preparation and full storage-writer composition,
static paths, event encoder/LOG path, then SetName public composition. StringBuffer only
specifies payload bytes, so partial-word proofs should mask the unused bytes rather than
assume zero padding. Reuse Reasoning.Memory.tailMask_toByteArray and storage arithmetic.

### SetName storage path and public proof

Completed StringMask (kernel-checked concrete masks, generic masked StringBuffer tail),
StringStorePrefix/Static/ShortStore, StringLongTail/LongStore, StringClearStart/Storage,
StringWriteState/Routines, StringSetStorage/Entry/Simulation. All have no placeholders.
The complete writer covers old-data clearing, short packed headers, full data-word loops,
masked partial tails, long headers, first-SSTORE static halts, invalid old-header panic,
event encoder11086 and LOG/STOP2399. Account maps match the source backend's exact write order;
no slot-noncollision hypothesis is used. StringSetSimulation connects the owner check and
all source outcomes after successful initial string allocation. Its focused build passed3636jobs.

SetName.lean now has its complete public proof and is LSP-clean. The focused public build
is running in /tmp/metamorpho-public-set-name-build.log; verify it before declaring SetName
finished. It composes the dispatcher, nonpayable branch, shared decoder, allocation failure,
and StringSetSimulation. All its helpers also support SetSymbol (Bool true), so that public
proof can follow after SetName's build passes. Remaining original placeholders become14
once SetName is validated; SetSymbol is still untouched at this checkpoint.

Proof performance: avoid `contradiction` on a context containing RD hypotheses; it unfolds
large runtime expressions before reaching a simple `some _ = none`. Use `cases hnone`
directly. Supply `(immWords := wordsOf (immStore v))` explicitly to generated packed summaries.
For a goal containing `D_J (deployedRuntime v)`, use PatchedValidJumps, not the Runtime variant.

### Both metadata setters completed

SetName's public build passed3657jobs (/tmp/metamorpho-public-set-name-build.log). SetSymbol's
public proof now reuses the shared Bool-parameterized helpers; its build also passed3657jobs
(/tmp/metamorpho-public-set-symbol-build.log). Both original statements/docstrings are preserved.
**13 original placeholders remain.** No new source correction beyond the recorded allocation
accounting change, and no new axiom declarations. StringMask's finite facts use decide +kernel.

Next selected function: SubmitMarketRemoval, selector39, entry5196. Begin with its source at
SpecSyntax1292 and existing MarketParams/cap-storage helpers. Do not switch away because an
internal dependency is difficult. No new mismatch has been identified.

### SubmitMarketRemoval completed

The original public theorem is fully proved and its focused build passed3683jobs
(`/tmp/metamorpho-public-market-removal-build.log`). **12 original placeholders remain.**
No source correction or new axiom was needed. CuratorRoleSource proves the modular curator
role call; MarketParamsCalldata/Fields/Decoder prove the complete five-word struct decoder,
its allocated memory, and its ID hash. MarketRemovalStorage/Syntax/GuardsSource/Source prove
the source outcomes; Role/Guards/Static/Store/Entry connect the runtime paths. The public
proof covers malformed calldata, nonpayable calls, role/guard rejection, checked timestamp
overflow, first-SSTORE static halt, packed timestamp update, event, and return.

Performance lesson: split Bool-dependent storage slots before applying storage-read lemmas.
Leaving `if pending then 16 else 13` in a mapping slot can make elaboration normalize crypto
for minutes. Likewise simplify the Bool-dependent returned word before using word equality.
Use explicit `(evm := evm)` where a local helper result has no expected type.

Next selected function: SetSupplyQueue, selector10, entry9964. Its calldata array remains in
calldata; it checks allocator role, length≤30, each market's cap, then writes slot20's array
and emits an event. Reuse storage-loop machinery and prior clear-loop proofs where possible.
No newly confirmed mismatch. Do not rerun the differential suite or initial audit.

### SetSupplyQueue completed

The original public theorem is fully proved. Its focused build passed3676jobs
(`/tmp/metamorpho-public-supply-queue-build.log`). **11 original placeholders remain.**
No source change, extra assumption, or axiom declaration was introduced.

AllocatorRoleSource proves the modular allocator-role call. DynamicCalldata,
WordArrayCalldata, CalldataArrayView, SupplyQueueEntry, and SupplyQueueRole cover complete
array decoding and authorization. SupplyQueueSyntax/CapCheck/Loop/Length/Source prove the
source and runtime validation loop and all reverts. SupplyQueueStorageSource,
WordArrayStorage/Algebra, and SupplyQueueStorageMatch establish exact storage equivalence.
SupplyQueueClearLoop/StorePrepare/WriteLoop/Finish/Static/Store complete all runtime paths.

The enormous old-length issue is resolved by finite gas. CountedStorageStep strengthens
RD.sstore to preserve its exact step count and positive gas cost. SupplyQueueClearLoop
proves a lower bound of40gas per iteration; lengths at least2^251-30 cannot finish.
For smaller old lengths, the concrete keccak(20) value establishes separation from slot20.
Zeroing order commutes even with repeated slots, and any cleared prefix is overwritten by
the new array. No mapping/array noncollision assumption was needed. The concrete data-base
hash uses native_decide; its numerical bounds use decide.

Generic config-cap reads now accept any bytes32-valued expression through
evalStorageRef_bytes32FieldExpr and SourceMemory.configCapRead. Existing public helper
statements remain available. All new proof files are below2000lines and width100.

Performance lesson: use `dsimp only [supplyQueueSourceState]` before rewriting its account
map. A `change` with metavariables for the source account-map arguments can normalize
crypto and recursive storage folds for minutes. Explicit residual stack arguments also
help when passing a generated RD summary through a `simpa`.

Next selected function: AcceptCap. Prove its `_setCap` internal dependency first and reuse
the existing expectedSupplyAssets and storage-array machinery. SubmitCap also uses this
dependency. Do not switch away because the dependency is difficult. No newly confirmed
mismatch; do not rerun the differential suite or initial audit.

### AcceptCap internal dependency completed

The complete allocated `_setCap` simulation now builds without placeholders:
`/tmp/metamorpho-set-cap-simulation-build.log`. It covers zero caps, existing markets,
new markets, both external readers, checked total-assets addition, queue events, final
packed storage writes, all revert branches, and all static-mode halts.

The previously authorized benchmark-local allocation repair was extended through
SetCapAllocationSyntax: allocatedSetCapFunction threads the allocation cursor through
expectedSupplyAssets; allocatedAcceptCapTransition supplies288 after its160-byte decoder
allocation. Spec registers this helper and uses the allocated transition for selector30.
SubmitCap still needs this repair when its proof is selected. No bytecode, Solidity,
generated blocks, shared library, or original public theorem signature was changed.

No storage noncollision premise was introduced. Queue reads occur after the actual
preceding writes. SetCapEventRuntime handles arbitrary resulting uint256 queue lengths
by finite induction, including memory-address wrap. SetCapSimulation needs account
presence internally; AcceptCapStorage.pendingCapPresent derives it from the public
nonzero pending timestamp, so the public theorem gains no assumption.

New proof modules include SupplyAssetsContinuation (reused by SupplyAssetsSimulation),
WordArrayRead, SetCapEnableSource/Runtime/Simulation, SetCapEventSource/Runtime,
SetCapReadersSimulation, SetCapFrames, SetCapFinishSimulation, SetCapNewMarketSimulation,
SetCapTailSimulation, and SetCapSimulation. Generic storage and allocation helpers also
include StorageAlias, LowBytesStorage, BoolByteStorage, and WordArrayPush.

AcceptCapSource and AcceptCapEntry build successfully3658jobs; AcceptCapGuards builds
successfully3644jobs. MarketParamsCalldataMemory proves decoded heap invariants;
MappingScratchMemory proves mapping-hash writes preserve heap bytes and the free cursor.
The public AcceptCap proof has now been written and is undergoing LSP validation.
Do not count its original placeholder as finished until the focused public build passes.
The other10 original placeholders remain untouched. AcceptCap remains selected.

Proof performance: give RD hypotheses explicit memory names before applying a generated
summary. Otherwise simp may miss a proved hash equality because the actual memory is
expanded into nested ByteArray.write expressions. UInt256 word equality uses u256_inj.

### AcceptCap completed

The original public theorem now builds successfully3782jobs:
`/tmp/metamorpho-public-accept-cap-build.log`. It covers complete ABI decoding, nonpayable
rejection, pending timestamp checks, and every allocated `_setCap` outcome. The original
statement and docstrings are preserved. **10 original placeholders remain.**

Next selected function: SubmitCap, selector18, entry8864. Reuse `_setCap` and the curator
role proof; establish its market last-update reader and both immediate/scheduled branches.
Stay with SubmitCap until complete; no differential suite or initial audit rerun.

### SubmitCap last-update dependency completed

SubmitCap remains selected. Its allocated last-update source/runtime simulation now
builds successfully3634jobs (`/tmp/metamorpho-last-update-simulation-build.log`). It covers
slot-hash addition overflow, singleton-array allocation, STATICCALL, call failure,
malformed returns, return-buffer and array allocation failures, empty-array rejection,
and uint128 truncation. LastUpdateSimulation preserves account storage, the decoded
MarketParams heap prefix, and the final free-memory cursor.

The authorized benchmark-local allocation repair was extended to SubmitCap in
SubmitCapAllocationSyntax/Spec/Common. The reader reserves160 bytes before its call,
threads the decoder cursor back to the caller, and supplies it to allocatedSetCapFunction.
This was announced before editing. No original theorem signature or generated file changed.

ExtSloadsSetup now exposes extSloadsEncodeReturn; ExtSloadsSimulation now exposes
extSloadsAfterBufferSimulation and extSloadsReturnValues_cons. Existing public helper
signatures are preserved and SupplySharesAllocationRoutines rebuilt successfully.

Next: public SubmitCap decoder, curator/asset guards, post-reader guards, immediate
_setCap branch, scheduled pending-cap writes and event, then public composition.
The original SubmitCap placeholder is still untouched;10 original placeholders remain.

### SubmitCap completed

The public SubmitCap theorem builds successfully3811jobs:
`/tmp/metamorpho-public-submit-cap-build.log`. The original statement and docstring
are preserved. **9 original placeholders remain.**

SubmitCapCalldata/Entry cover the tuple-plus-cap decoder and nonpayable rejection.
SubmitCapRole/Asset prove the authorization and asset guards. SubmitCapSyntax and
PrefixSource connect these to the allocated last-update reader. Guards/GuardsSource,
Uint184Cast, ImmediateSource/Simulation, ScheduleSource/Runtime/Static, and TailSimulation
cover both branches and every revert/static outcome. PendingCapStorage captures the
timelock before the first packed write, matching bytecode without a slot noncollision
assumption. The lower branch reuses SetCapSimulation and derives account presence from
the positive old cap. The tail and last-update simulation build passed3774jobs:
`/tmp/metamorpho-submit-cap-tail-build.log`.

Shared factoring: ScalarTupleABI.scalarTupleValueDecode now supplies the existing
MarketParamsCalldata and scalarTupleReturnDecode proofs. MarketRemovalSyntax exposes
marketParamsTupleStructSource. Original helper APIs remain intact.

Next selected function: UpdateWithdrawQueue, selector20, entry7984. Remain with it until
complete. The remaining functions are UpdateWithdrawQueue, Permit, Multicall, Deposit,
Mint, Withdraw, Redeem, Reallocate, Constructor. Do not rerun the differential suite or
initial audit. Main-thread-only proof work continues.

### UpdateWithdrawQueue allocation and first loop

UpdateWithdrawQueue remains selected;9 original placeholders remain. The authorized
benchmark-local cursor correction now covers its two word-array reservations and the
allocated supply-share calls in its removal loop (UpdateWithdrawQueueAllocationSyntax,
Spec/Common). Generated artifacts and original public signatures are unchanged.

Entry, role, UintArrayCalldata, explicit Syntax, both runtime/source allocation paths,
and the full first-loop simulation pass LSP. Allocation source build passed3566jobs:
`/tmp/metamorpho-update-withdraw-queue-allocation-source-build.log`. First-loop focused
build passed3666jobs in `/tmp/metamorpho-update-withdraw-queue-build-loop.log`.

New memory machinery: WordArrayInitMemory exposes sparse-gap zero reads and reuses
Attester.wordArrayHeaderMemory facts; WordArrayPrefix tracks initialized array prefixes.
UpdateWithdrawQueueMemory proves initialization, scratch preservation, and per-step writes.
UpdateWithdrawQueueReady captures source locals through both loops. BuildSource proves
bounds/duplicate reverts and success; BuildRuntime proves the matching8690→8163 iteration;
BuildLoop composes these to8171, preserving the initialized arrays and free pointer.

Shared factoring: ArrayStorage.evalStorage_withdrawQueue_local now supports any local
index name; old evalStorage_withdrawQueue and accruedAssetsQueueRead APIs delegate to it.
CalldataArrayIndexRuntime contains the former SupplyQueueCapCheck indexing helpers;
SupplyQueueCapCheck imports it. WordArrayIndexRuntime covers the memory-array index routine
at12057, address normalization, and withdrawal-queue out-of-bounds reversion.

Next: removal loop8175→8183, then final storage replacement/event and public composition.
Maintain fresh storage-array bounds at each read: config deletion may alias queue storage;
do not assume slot noncollision or a30-element bound. SupplySharesAllocationRoutines and
its memory-prefix lemmas are already proved and must be reused. No suite/audit rerun.

### UpdateWithdrawQueue removal loop

The complete removal-loop simulation now passes LSP: RemoveSelect, RemoveRuntime,
RemoveSource, Reader, RemovalTailSource/Runtime, Delete, Omitted, and RemoveLoop.
UpdateWithdrawQueueHeap preserves the two completed arrays as external reader calls
advance the allocation cursor. MarketConfigDeletion proves that clearing all three
packed fields matches a zero-word write. LocalArrayBoolSource factors the local bool
array condition shared by both loops. BuildSource now uses this shared helper.

RemoveLoop covers fresh array-bound rejection, cap/pending-cap rejection, all allocated
supply-share reader outcomes, timelock rejection, static SSTORE, and successful deletion.
It threads SourceState, local variables, arrays, and the cursor to PC8183. The retained
path leaves the state unchanged. A focused removal/first-loop rebuild is next, followed
by final queue storage replacement, event, and public composition. No new assumptions.

### UpdateWithdrawQueue completed

The public theorem passes LSP and its focused build passed3734jobs:
`/tmp/metamorpho-public-update-withdraw-queue-build.log`. The original public statement
and docstring are preserved. **8 original placeholders remain.**

The removal/first-loop build passed3685jobs:
`/tmp/metamorpho-update-withdraw-queue-remove-loop.log`. The final storage tail and existing
SetSupplyQueue theorem passed3712jobs: `/tmp/metamorpho-update-withdraw-queue-store.log`.

StorePrepare, ClearLoop, WriteLoop, Finish, StoreStatic, TailSource, Storage, and Store
prove replacement, gas exhaustion for enormous cleanup lengths, static failure, and return.
Loops composes both loops with the tail; Simulation handles both allocation reservations
and all allocation failures; UpdateWithdrawQueue joins decoder, role, and body simulation.

WordArrayStorage now contains generic replacement-backend and list-indexing lemmas.
WordArrayStorageAlgebra exposes source/runtime replacement accounts and their equality
under proved header/data separation; clearWordArray_shift removes an unnecessary count
bound from the older helper. SupplyQueueStorageSource/Match use these shared lemmas with
unchanged APIs. Withdrawal-queue separation uses concrete keccak evaluation and the
cleanup gas bound, not an added assumption. Formatting checks cover all new modules.

Next selected function: Permit, selector65, entry1586. Remain with it until complete.
Remaining: Permit, Multicall, Deposit, Mint, Withdraw, Redeem, Reallocate, Constructor.
No differential-suite or initial-audit rerun; no subagents; no commits/staging.

### Permit completed

The public Permit theorem passes LSP and its focused build passed 3669 jobs:
`/tmp/metamorpho-public-permit-build.log`. The original public statement and docstring
are unchanged. **7 original placeholders remain:** Multicall, Deposit, Mint, Withdraw,
Redeem, Reallocate, Constructor. No added assumptions or Permit specification changes.

Signature recovery is complete in ECDSATrySource/Return, ECDSAErrorSource,
ECDSARecoverSource, EcrecoverOutput/ABI/Memory/Call, ECDSATryRuntime,
ECDSAErrorRuntime, ECDSARecoverRuntime, and ECDSASimulation. The precompile's output
shape is derived from its semantics, including empty output, canonical addresses,
call/depth failure, high-s rejection, zero signer, and success. The recovery simulation
build passed 3600 jobs (`/tmp/metamorpho-permit-recovery-simulation-build.log`).
Earlier source/helper builds: `/tmp/metamorpho-permit-hash-helpers-build.log` (3541 jobs),
`/tmp/metamorpho-permit-recovery-source-build.log` (3520 jobs).

NonceSource models the wrapping nonce increment, source calls, and static execution.
PermitHashSource/Memory/Runtime and PermitNonceRuntime/Static prove the actual nonce
store, six-word preimage, allocation, and hashing. Their build passed 3604 jobs:
`/tmp/metamorpho-permit-nonce-hash-build.log`. TypedDataHashSource/Memory/Runtime,
DomainCursorMemory, and TypedDataDomainRuntime cover both domain-cache branches and
the EIP-712 envelope. PermitDigestRuntime composes these with the nonce operation.

PermitData, PermitPrefixSource, PermitTailSource, PermitApprovalRuntime, and
PermitBodySimulation connect source execution to recovery and approval. Body simulation
build passed 3643 jobs (`/tmp/metamorpho-permit-body-simulation-build.log`). PermitABI
and PermitEntry cover short/huge calldata, both noncanonical addresses, noncanonical
uint8, nonpayable calls, and deadline rejection. CalldataValueDecode supplies reusable
selector-relative static-field decoding, including bytes32.

Shared factoring: WordPrefixMemory generalizes WordCallMemory to arbitrary short prefixes;
PackedWordsMemory handles allocated word preimages, with DomainMemory delegating to it.
PackedSource.evalExpr_addressToWord removes repeated address-word encoding work from
DomainHashSource and PermitHashSource. New Permit/recovery files and auxiliary modules
contain no sorry/admit/axiom declarations. All files are below 2000 lines.

Next selected original function: Multicall. Stay with it until complete, working through
its dependencies first. No differential-suite or initial-audit rerun; main thread only;
no commits or staging. Public Permit build is complete; no build remains running.

### Multicall completed

The public `metaMorphoV1_1MulticallBody` now passes LSP and its focused build (3717 jobs),
recorded in `.multicall-final-build.log`. Its statement is unchanged. Six original
placeholders remain: Deposit, Mint, Withdraw, Redeem, Reallocate, Constructor.

Two source repairs were reported when discovered. `MulticallCalldataSyntax` selects the
new solc08 calldata-reference plan for the bytes[] signature, preserving signed/wrapping
relative-offset checks and deferring invalid elements until the iteration that accesses
them. `MulticallAllocationSyntax` checks the deferred decode-failure marker before copying
an element. `Spec.config.externalABI.decodeCalldata?` routes this signature through the
plan and leaves other signatures on the prior decoder. No Solidity, bytecode, generated
block, shared library, or public theorem statement changed.

CalldataReference/Bytes, BytesArrayCalldata/Head/Decode/Element, BytesTailBounds,
MulticallABI/Input/Entry and MulticallCalldataRuntime prove decoding and per-element
copying. DelegateCallSource/Runtime and MulticallDelegateSimulation compose the generic
self-DELEGATECALL semantics, allocation failures, call-depth failure, and result checks.
ByteMemoryPrefix and BytesBuffer preserve unpadded raw return buffers; MulticallMemory,
MulticallStepMemory and MulticallStoreRuntime track the result pointer table. Source
frames and statements are in MulticallReady/ElementSource/CallSource; MulticallIteration
and MulticallLoop prove all iterations. MulticallInitialMemory/InitLoop/AllocationRuntime
and MulticallPrefixSource cover allocation and initialization, including its failure path.

BytesArrayReturnABI, BytesArraySources, StringEncoderBytePrefix, BytesArrayEncodeStep/Read/
Runtime and MulticallReturnMemory/Runtime encode the full bytes[] return. The output-size
bound is derived from allocated array and element bounds. MulticallSimulation composes
these modules with source execution. Its build passed 3691 jobs. No added assumptions,
sorries, admits, or axiom declarations in these helpers.

The public multicall axiom check is `.multicall-axioms.log`: all 1255 entries are
`propext`, `Classical.choice`, `Quot.sound`, or existing/concrete `native_decide`
evaluation axioms. No `sorryAx` or unexpected axiom occurs. The full Correct checkpoint
passed 4342 jobs in `.multicall-correct-checkpoint.log`; its six remaining original
placeholders are expected until subsequent work completes.

Next selected original function: Deposit. Stay with it until complete; reuse its shared
accrue-interest, conversion, safe-transfer and mint proofs, and prove the mutating supply
loop. No differential-suite or initial-audit rerun, subagents, commits, or staging.


## Deposit progress: complete mutating supply helper (2026-10-14)

Deposit remains the selected original function. Its public theorem is still a placeholder;
no new placeholders or axioms were introduced. The original remaining leaves are Deposit,
Mint, Withdraw, Redeem, Reallocate, and Constructor.

The ERC4626 transfer/mint/event composition is proved in `ERC4626DepositSimulation.lean`.
The allocated mutating supply helper is now proved in `SupplyMorphoSimulation.lean` (LSP
clean; focused build log `.deposit-supply-loop-build.log`). It composes market parameter
reads, the code guard and Morpho accrual CALL, the market/position reads, rounded-up asset
conversion, branchless capacity/minimum arithmetic, optional supply CALL with catch, and
all loop paths. The loop uses `UInt256.size - i.toNat`, rereads queue length after calls,
and does not assume that accrual or supply preserves storage. The new source allocation
propagation in `DepositAllocationSyntax.lean` / `SupplyMorphoAllocationSyntax.lean` is
already wired into `Spec.lean`; this correction was reported when made.

Key layers are `SupplyMorphoReadersSimulation`, `SupplyMorphoArithmeticSimulation`,
`SupplyMorphoAttempt`, `SupplyMorphoTail`, `SupplyMorphoIteration`, and `SupplyMorphoLoop`.
`SupplyLoopLocals` tracks contract, immutables, target, index, assets, cursor, and absent
storage-shadowing locals. The successful helper theorem returns free-pointer equality,
64-bit cursor bound, cursor monotonicity, and heap-prefix preservation, with runtime
control transferred to an arbitrary valid return PC. It requires 25 stack slots beyond R,
96 <= input cursor, 96 <= input memory size, and bounded calldata; no callee assumptions.

Runtime CALL support is split into `MorphoAccrueCall`, `SupplyMarketSimulation`, and
`MorphoSupplySimulation`, with encoder/decoder and allocation modules. The shared
`MarketReturnAllocation` and `MarketReadSimulation` proofs were refactored through
`MarketReadDecode`; public interfaces are retained. `Minimum.lean` now proves that the
compiler's subtraction-based zero test agrees with its xor-selected minimum.

Build checkpoint: `lake build Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoIteration
Benchmarks.Morpho.MetaMorphoV1_1.Correct` succeeded (4375 jobs), log
`.deposit-iteration-checkpoint.log`. Existing six sorry warnings remain. Earlier focused
builds `.deposit-market-build.log`, `.deposit-supply-call-build.log`,
`.deposit-source-readers-build.log`, `.deposit-readers-build.log`, and
`.deposit-supply-attempt-build.log` succeeded. `git diff --check` was clean. No final
capstone axiom audit has run yet; do not rerun differential tests or the initial audit.

Next: connect the supply return at PC 14745 to checked lastTotalAssets + assets, the
existing `updateLastAssetsReturn` (PC 16830), and return via 14753. Then compose allocated
ERC4626 + supply + update into `allocatedDepositFunction`, followed by the public deposit
entry (7351), interest accrual, conversion, and final ABI return. Runtime 14745 reads slot22
at the actual post-supply state and jumps to checked addition12077 with stack
[lastTotalAssets, assets,13745,14753,ret]++R. Block13745 transfers to16830;
updateLastAssetsReturn returns14753 with [ret]++R;14753 jumpsret. Preserve the original
statement and finish Deposit before switching to another original function.

## Deposit completed (2026-10-14)

`metaMorphoV1_1DepositBody` is now proved with its original statement. Its proof covers
entry guards, two-argument ABI decoding, accrual reverts and static failure, checked share
conversion, token transfer, share minting/event, the full mutating Morpho supply loop,
post-supply lastTotalAssets addition/update, and ABI return. `DepositFinishSource` and
`DepositFinishSimulation` use the actual post-supply storage state. `DepositInternalSource`
and `DepositInternalSimulation` compose the complete internal helper. `DepositPublicSource`,
`DepositPublicSimulation`, `DepositEntry`, and generic `UintAddressCalldata` finish the entry.

Build `lake build Benchmarks.Morpho.MetaMorphoV1_1.Deposit
Benchmarks.Morpho.MetaMorphoV1_1.Correct` succeeded (4393 jobs), log
`.deposit-final-build.log`. Focused internal/helper builds also succeeded. The public
deposit axiom check is `.deposit-axioms.lean` / `.deposit-axioms.log`. No new placeholders,
assumptions, or axiom declarations. `git diff --check` passes.

Five original leaves remain: Mint, Withdraw, Redeem, Reallocate, Constructor. Next
selected original function is Mint; reuse the completed internal deposit proof and
rounded-up assets conversion. Its transition still uses the original unallocated calls,
so inspect its cursor propagation before wiring its source proof. Keep all changes inside
this contract directory. Do not rerun differential tests or the initial audit.

## Mint completed (2026-10-14)

`metaMorphoV1_1MintBody` is proved with its original statement. `MintPublicSource`,
`MintPublicSimulation`, and `MintEntry` reuse the completed deposit internals and
`ConvertAssetsUpRoutines`. Allocation tracking was corrected and reported: the new
`allocatedMintTransition` in `DepositAllocationSyntax` routes accrual and deposit through
the cursor-aware helpers; `Spec.lean` and its selector normalization are wired accordingly.

Mint is LSP-clean and its Lake target built successfully in `.mint-final-build.log`.
The public axiom check `.mint-axioms.log` contains only the accepted base (4797 entries,
no `sorryAx` or unexpected axioms). Deposit's check has 4581 accepted entries. The focused
allocation rebuild passed 3843 jobs in `.mint-allocation-build.log`; the full Correct
checkpoint is in `.mint-final-build.log`. The new Mint helper files have no placeholders.

Next selected original function: Withdraw. Stay with it until complete. Four original
placeholders remain: Withdraw, Redeem, Reallocate, Constructor. Withdraw's public entry is
3446, ABI decoder11559, accrue14262/return3475, upward shares14419/return3491,
internal withdrawal15525. Existing `WithdrawLoop*` proofs cover the read-only simulation,
not the mutating `_withdrawMorpho`. The latter calls `_accruedSupplyBalance`, which first
CALLs Morpho.accrueInterest, then reads market and shares, converts down, and returns a
market struct; it must handle arbitrary CALL state changes. Reuse `MorphoAccrueCall`,
`SupplyMarketSimulation`, `SupplySharesAllocationSimulation`, `WithdrawableSimulation`,
and the completed supply loop pattern. ERC4626 withdrawal needs allowance, burn, and the
already-proved `safeTransferSimulation` before its event. No Withdraw edits yet.


## Withdraw internal stages completed (2026-10-14)

The allocation correction was reported and implemented in `WithdrawAllocationSyntax`:
`allocatedAccruedSupplyBalanceFunction`, `allocatedWithdrawMorphoFunction`,
`allocatedERC4626WithdrawFunction`, `allocatedWithdrawFunction`, and public transition54.
Spec appends the helper functions and routes the transition; old function indices stay fixed.
Accrued supply balance includes the actual Morpho accrueInterest CALL state, then market
and shares reads. All CALL effects are threaded; there is no storage-invariance assumption.

Completed helper groups: `AccruedSupply*` (3682-job focused build), `MorphoWithdraw*`
(3624 jobs), `WithdrawMorpho*` (3738 jobs). The latter proves the complete mutating market
loop, rereading withdrawal queue length and each market against the actual latest state,
catching failed Morpho withdrawals, checking allocation/return decoding, and exhausting
remaining assets or reverting. Memory prefixes and cursor bounds are preserved.

`BurnSupplySource`, `BurnInternalSource`, `WithdrawBurnRoutines`, `ERC4626WithdrawSource`,
`WithdrawAllowanceMemory`, `WithdrawVaultState`, and `WithdrawAllowanceSimulation` prove
allowance and burn with the supply storage read after the balance debit. The strengthened
`safeTransferHeapSimulation` preserves memory/cursor facts; the original safeTransferSimulation
signature remains as a wrapper. `ERC4626WithdrawSimulation` connects allowance, burn,
safe transfer, and the Withdraw event; its focused build passed 3803 jobs.
`WithdrawInternalSource` and `WithdrawInternalSimulation` connect the accounting update,
market loop, and ERC4626 helper; `.withdraw-internal-build.log` passed 3861 jobs.

Public helpers `WithdrawPublicSource` and `WithdrawPublicSimulation` are LSP-clean and
built (`.withdraw-public-source-build.log`, `.withdraw-public-simulation-build.log`).
`UintTwoAddressesCalldata` and `UintTwoAddressesDecoder` prove the full three-word ABI
case, including both noncanonical addresses. `WithdrawEntry` builds (3516 jobs).
`Withdraw.lean` now contains the candidate complete original Body proof and is currently
being built in `.withdraw-body-build.log`. Do not switch original functions until it is
validated. Then run the Correct checkpoint and public axiom check before Redeem.
No differential suite or initial audit reruns. No edits outside this directory.


## Withdraw public proof completed (2026-10-14)

`metaMorphoV1_1WithdrawBody` is LSP-clean and built successfully in the ongoing
`.withdraw-final-build.log` Correct checkpoint. Its unchanged statement is proved for all
valid and malformed calldata branches, reverts/static failure, accrual, conversion, the
internal helper, and the return encoding. `.withdraw-axioms.log` has only propext,
Classical.choice, Quot.sound, and native_decide evaluation axioms; no sorryAx.
The top-level checkpoint was still rebuilding dependent leaves when this note was added.

Redeem is now selected. The missing cursor propagation was reported. Public source,
simulation, entry, and candidate Body files have been prepared using the completed
withdrawal internals and existing downward conversion. Before validation, wire
`allocatedRedeemTransition` (same transformation as allocatedWithdrawTransition, source56)
into Spec and Common selector normalization. Wait for the current Correct build before
mutating Spec to avoid racing its snapshot. No source functions need to be appended.


Withdraw Correct checkpoint completed successfully (4436 jobs) in `.withdraw-final-build.log`.
The public axiom footprint has 5384 accepted entries, with no unexpected axiom.
Redeem allocation is now wired via `RedeemAllocationSyntax`, transition56 in Spec, and
its Common selector lemma. The candidate public source/simulation build is running in
`.redeem-public-build.log`. Entry/allocation modules passed 3517 jobs beforehand.


## Redeem completed (2026-10-14)

`metaMorphoV1_1RedeemBody` is proved with its original statement. Its allocation-aware
transition and source/bytecode public composition reuse `withdrawInternalSimulation`,
`convertAssetsReturn`, and `UintTwoAddressesDecoder`. The focused build passed 3899 jobs
in `.redeem-body-build.log`; the public axiom check is `.redeem-axioms.log`.
The first public helper build hit concurrent missing .olean artifacts; the subsequent
complete target build restored consistent dependencies and passed. Avoid simultaneous
LSP import rebuilds and shell Lake builds immediately after editing Spec/Common.

Next selected original function is Reallocate (transition34, entry in Reallocate.lean).
Only Reallocate and Constructor remain. Keep both original theorem statements unchanged.
Current source inspection is `.reallocate-inspect.lean`; no reallocate implementation
changes yet. HANDOFF history was split to preserve the 2000-line limit; earlier progress
is in HANDOFF_HISTORY_2026_10_14.md. No differential/audit reruns or outside edits.

## Reallocate implementation checkpoint (2026-10-14)

Reallocate remains the selected original leaf. Constructor is the only other original
unfinished leaf. The source now uses deferred per-row calldata decoding and explicit
allocation cursors. Malformed rows are checked immediately after indexing, before tuple
projection; this correction was reported when found. The allocation rewrite reserves
64+160 bytes per row, calls the allocation-aware accrued-balance helper, and reserves
64 bytes for each strict external-call result. `.reallocate-guard-spec-build.log` built
Spec and ReallocateSyntax successfully. No generated summaries, bytecode, Solidity,
outside files, differential suite, or audit were changed/run.

Completed and built modules:
- ReallocateCalldataSyntax, ReallocateCalldata, ReallocateABI: deferred ABI array plan,
  raw decoder and values/get facts; MulticallCalldataSyntax dispatches the reallocate plan.
- ReallocateWithdrawEncode/Return/Simulation and ReallocateSupplyEncode/Return/Simulation:
  strict same-call correspondence, call failure, short return, and return allocation.
- CalldataAddressRoutine, CalldataWordWindow, ReallocateRowABI/Fields/Memory/Enabled/Allocation:
  row decoding, address canonicality, memory, ID/config guard, and 224-byte reservation.
- ReallocateSyntax: literal row/branch/loop fragments and transition-body identity.
- ReallocateRowSource, ReallocateReserveSource, ReallocateRowHeap, ReallocateRowPrefix:
  source declarations, sentinel revert, reserve, memory facts, and 5985-to-6152 simulation.
- ReallocateLocals, ReallocateBalancesSource, ReallocateAccruedSimulation:
  loop-local invariant and source/runtime accrued-balance composition to PC6162.
- ReallocateArithmeticSource, ReallocateAmountRuntime: clamped withdrawal amount and
  full-withdrawal asset/share selection.
- StrictPairCallSource, ReallocateCallSource: strict calls plus 64-byte source reservations.
- ReallocateEventStatic/Runtime, ReallocateWithdrawFinishSource/Runtime: event and checked total.
- ReallocateWithdrawBranch: complete branch from PC6182 to PC6380, including revert,
  static violation, and successful source/memory/invariant preservation. Explicit build
  `.reallocate-withdraw-branch-build.log` passed 3706 jobs.
- ReallocateSupplyAmountSource: first three source statements and zero/nonzero continue
  choice. Explicit build `.reallocate-supply-amount-source-build.log` completed.

Current next work: supply cap/source/runtime and finish, then whole supply branch,
row/iteration/loop, ABI entry/role/public Reallocate. Do not switch to Constructor yet.
No fresh full Correct or public axiom checkpoint since the earlier Redeem checkpoint.

Runtime stack map (the dispatcher leaves a saved selector word, required by DUP10):
- Loop5954: [totalW,offset,i,len,totalS,saved]++R.
- Row5985: [remaining,totalW,base,offset,i,len,totalS,saved]++R;
  base=offset+192*i, remaining=size-base-36.
- Prefix6152: [allocation+32,allocation,totalW,id,offset,i,len,totalS,saved]++R.
- Accrued6162: [marketPtr,shares,assets,allocation+32,allocation,totalW,id,offset,i,len,totalS,saved]++R.
- Amount6182/6450: [target,assets,shares,allocation,allocation+32,amount,totalW,id,offset,i,len,totalS,saved]++R.
- Supply6479: [assets,allocation,totalS,suppliedAmount,id,offset,totalW,len,i,saved]++R.
- Supply6526: [allocation,totalS,suppliedAmount,id,offset,totalW,len,i,saved]++R.
  Generic reallocateSupplySimulation calls its second stack variable `id`, but this
  invocation supplies totalS there and the actual ID as its fourth variable `x`.
- Supply6716: [outShares,outAssets,id,totalS,suppliedAmount,6686,1,offset,totalW,len,i,saved]++R.
- Loop increment6380: [i,1,offset,totalW,len,totalS,saved]++R.

Build/proof lessons: explicit evm/evm' arguments avoid huge unresolved source-call
metavariables; pass immWords explicitly to generated/runtime static lemmas. Parenthesize
multiline locals := insert terms. `rfl` against unresolved if/match branches may time out;
use by_cases plus simp only instead. Avoid concurrent LSP dependency and Lake builds.


## Reallocate public composition checkpoint (2026-10-14)

The supply branch and loop are now complete. Completed focused builds:
- ReallocateSupplyAmountRuntime, ReallocateSupplyCapSource/Runtime: amount/continue,
  checked supply-cap comparison, and its revert paths.
- ReallocateSupplyFinishSource/Runtime, ReallocateSupplyBranch: strict supply call,
  result allocation, event, checked total, static violation, and preserved heap/locals.
- ReallocateRowContinuation, ReallocateIteration: complete row from PC5985 to6380.
- ReallocateLoopData, ReallocateLoop: calldata row bounds and induction over remaining
  rows, preserving the actual post-call state and handling both normal and continue bodies.
  `.reallocate-loop-build.log` succeeded.
- ReallocateCalldataChecks: deferred decoder agrees with all outer compiler checks;
  accepted calldata supplies the loop invariant. `.reallocate-calldata-checks-build.log` succeeded.
- ReallocateEntry, ReallocateRole: nonpayable/outer decode and allocator-curator-owner
  authorization, PC5836→5916→5949. `.reallocate-entry-role-build.log` succeeded (3683 jobs).
- ReallocatePublicSource, ReallocateFinishRuntime: source initialization and final
  totalWithdrawn==totalSupplied check, PC6789→STOP6796/revert6797.
  `.reallocate-public-deps-build.log` succeeded (3679 jobs).

ReallocateSimulation composes the public source/runtime including static violations,
reverts, and successful empty return. LSP passed. The original public theorem in
Reallocate.lean has now been replaced with its intended proof, with original statement.
The focused `.reallocate-body-build.log` is running at this checkpoint; check its final
status before treating Reallocate as complete. Then check the public theorem's axioms.
Only after that switch to the original Constructor leaf, the last original placeholder.

Elaboration lesson: do not use `rfl` for `x = 0 + x` when x unfolds calldata decoding.
Use `(Nat.zero_add _).symm`; otherwise elaboration needlessly expands the whole decoder.
Also normalize SourceState.env in both the role result and its free-pointer proof before
applying the loop theorem. Explicit loop parameters make this composition cheap.
No full Correct/axiom checkpoint since Redeem yet. No differential/audit reruns.


Reallocate is complete: `.reallocate-body-build.log` passed 3844 jobs and the public
axiom check `.reallocate-axioms.log` contains only the accepted trusted base, no sorryAx.
All runtime leaves are complete. Constructor is now the only selected unfinished leaf.


## Constructor input-domain decision (2026-10-14)

The constructor is the only original unfinished leaf. Its unchanged target is
`typedConstructorRefinement`, which does not bound initcode length. The unchanged
`config.selfDeployment` uses `genSolidityConstructorDeployment` and accepts strings
of arbitrary mathematical length. The compiler is solc 0.8.37, viaIR, optimizer 200,
Cancun. Creation bytecode length23666, embedded runtime offset3894. Initial allocation
cursor480; PC12 computes CODESIZE-23666 and calls allocator2608 before copying args.

A symbolic, Lean-checked `ConstructorSizeWitness.lean` establishes an input collision:
- arguments n = owner1, morpho2, initialTimelock0, asset3, n zero name bytes, empty symbol;
- for paddedSize n=n, deployment accepts this encoding, of length256+n;
- at n=UInt256.size, the name length word wraps to0 and the symbol offset wraps to224;
- the first256 argument bytes equal the empty-name encoding, and CODESIZE words agree;
- the source name differs, and its storage-header encoding is1 versus0 for the empty name.
`admittedInput_wraps` bundles admission, actual oversize, equal copied prefix, equal
CODESIZE word, and differing source input. This is a certified encoding collision,
NOT a complete negation of the refinement or a full Xi execution counterexample.
No massive array is materialized; this is a symbolic proof, not differential testing.

The existing library has `Stele/RefineWithCodeBound.lean`, used by Comet after that task's
user explicitly approved a deployment-domain change. That approval DOES NOT authorize
changing this task. `ConstructorCodeBound.proposed.patch` is a concrete UNAPPLIED proposal:
import the library, use typedConstructorRefinementWithCodeBound for Constructor, and
contractRefinementWFWithCodeBound trivialStorageWF noGasBound for the capstone. It adds
only the deployment premise I.code.size<UInt256.size, leaving config/deployment/runtime
unchanged. It needs explicit approval because this user's goal forbids extra assumptions.
A pending asynchronous question requests that decision. Do not apply the patch or continue
dependent constructor work without resolution. No source/config/theorem change was made.

The focused build of Correct and ConstructorSizeWitness is running in
`.constructor-size-review-build.log` at this checkpoint. Then run the prepared
`.constructor-size-axioms.lean` and `.runtime-axioms.lean` and check accepted axiom names.
This is the FIRST goal turn encountering this input-domain decision. Keep the goal active;
do not mark complete/paused/blocked now. If the same impasse recurs in three consecutive
goal turns without resolution, follow the goal tool's blocked threshold.

Proof lesson: large numeric literals as the right operand of symbolic Nat.add can trigger
kernel deep recursion during word conversion. The generic `wordOfNat_eq_of_mod` avoids
reducing its arguments while converting residue equality to UInt256 equality.


Validation completed for the constructor-domain review:
- `.constructor-size-review-build.log`: Correct and ConstructorSizeWitness built successfully,
  4494 jobs. The sole original sorry remains Constructor.lean:18.
- `.runtime-axioms.log`: metaMorphoV1_1RuntimeCorrect has22763 accepted axiom dependencies,
  standard Lean axioms/native_decide certificates only, no sorryAx or custom assumptions.
- `.constructor-size-axioms.log`: admittedInput_wraps has4 accepted dependencies;
  sourceStorageHeader_differs has1. No sorryAx/custom assumptions.
- The proposed code-bound patch remains unapplied. Constructor.lean and Correct.lean are
  unchanged from their earlier theorem statements; Spec was not changed for this issue.
- No build or tool process remains running. The asynchronous domain-choice question has
  no reply yet. This remains the first goal turn on the boundary decision.


## Constructor-domain continuation: second goal turn (2026-10-14)

The previous goal turn was progress: it completed Reallocate/all runtime proofs and
produced the checked constructor encoding collision. This second turn revalidated the
current original theorem, encoder, untouched Constructor/Correct files, and remaining
single sorry. No approval for the pending domain-choice question has arrived; the automatic
goal continuation is not approval to add a premise.

The witness was strengthened without changing the model or target:
- `deployment_doesNotImplyCodeBound` proves the proposed bound cannot be deduced from
  successful deployment encoding, so it would genuinely narrow the theorem's domain.
- `copiedLength_wraps` proves the actual constructor CODESIZE-23666 expression is256.
- `copiedArgumentWindow` proves the requested256-byte argument window is exactly the
  ordinary empty-name encoding.
These facts narrow the investigation but still do not constitute a complete Xi execution
counterexample. `.constructor-size-followup-build.log` passed3512 jobs. The corresponding
`.constructor-size-followup-axioms.log` shows only standard/native_decide dependencies.
No original theorem, config, generated block, bytecode, or external file changed.

The same input-domain decision remains unresolved for two consecutive goal turns.
No build/tool process remains running. Leave the goal active this turn. On a third
consecutive occurrence, if no authorization or other resolution arrives and meaningful
progress still requires that decision, use update_goal(status="blocked") per the goal rules.
Do not repeat the permission request or treat elapsed time as approval.


## Constructor-domain continuation: third goal turn (2026-10-14)

The prior turn was progress: it strengthened and checked the boundary witness. This third
turn revalidated the actual source and terminal build/axiom results. The original constructor
and capstone statements and deployment encoder remain unchanged; the sole sorry is still
Constructor.lean:18. The proposed bound remains unapplied and no approval or alternative
resolution has arrived. There is no running job to wait for and no remaining runtime work.

The same constructor-domain impasse has now persisted for three consecutive goal turns.
Proceeding with the proposed domain restriction would violate the explicit no-extra-assumptions
requirement without user authorization. The goal is being marked blocked, not complete.
Resume after the user resolves the domain decision; a later resumed run starts a fresh blocked
audit. The witness remains an encoding/copy-window collision, not a full Xi counterexample.


## Constructor code bound approved and applied (2026-10-14)

The user explicitly instructed "Apply the proposed patch" and resumed the goal. This
authorizes the specific deployment premise `I.code.size < UInt256.size` and supersedes
the pending-decision/blocked instructions above. `ConstructorCodeBound.proposed.patch`
has now been applied to Constructor.lean and Correct.lean: the constructor uses
`typedConstructorRefinementWithCodeBound`, and the capstone uses
`contractRefinementWFWithCodeBound trivialStorageWF noGasBound`. The other original
constraints remain in force. Continue the constructor proof without asking for this
authorization again. The constructor's original sorry still needs to be discharged.

The applied patch required the standard runtime adapter in Correct.lean:
`fun imms hfit => runtimeRefinementWithWF_trivial_iff.mpr
  (metaMorphoV1_1RuntimeCorrect imms hfit)`.
`.constructor-code-bound-build.log` passed 4493 jobs. The adapter adds no runtime
condition. `.constructor-entry-build.log` subsequently passed 4500 jobs before the
constructor source allocation change below.

Constructor progress after approval:
- `ConstructorEncoding.lean`: typed six-field ConstructorArgs; canonical encoding,
  length/alignment, exact deployment inversion, bounded shape, and exact
  CODESIZE-23666. ConstructorSizeWitness now reuses its creation-size fact.
- `ConstructorAllocation.lean`: creation allocator2608/2639 and panic1854, both
  branches, using the same checked source allocator as runtime (the lor/land operands
  are reversed in creation code).
- `ConstructorEntry.lean`: generic arbitrary-argument revert packaging, completed
  nonpayable branch, entry0->12->2608, initial allocation success->29/revert.
- `ConstructorAllocationSyntax.lean`: constructor-only source correction, attached
  as contract.ctor in Spec.lean. Preserve first nonpayable guard, then reserve encoded
  args from480, name(32+padded), symbol(32+padded), and literals32,32,32,64, before
  the original first storage write. This addresses actual compiler allocation
  failures; it does not add an assumption. Remaining constructor allocations/call
  cursor threading still need source modeling as their proofs are developed.
- `ConstructorInputSource.lean`: source padded/encoded length, typed parameter frame,
  source initial-allocation failure and combined refinement for that branch.
  `.constructor-model-build.log` passed3525 jobs; `.constructor-input-source-build.log`
  passed3526 jobs. No new sorry/axiom in these helper modules.
- Constructor.lean now extracts typed deployment, handles nonpayable and initial
  allocation failure; its sole original sorry remains on nonpayable-zero / allocation
  success. Next: copy/decode arguments fromPC29, then string allocations, literal
  allocations and initialization/body calls. All runtime selectors remain proved.

Proof lesson: use `Reasoning.Theory.encodeABIValue_uint256` instead of expanding its
encoding inside the six-field constructor encoding proof; the expanded proof triggered
kernel deep recursion. For source maps constructed with ofList, use
`Std.HashMap.getElem?_ofList_of_mem` with distinct-key and membership proofs.

Further constructor progress in the same approved-patch turn:
- `ConstructorArgumentMemory.lean`: aligned argument-size rounding, equivalence of
  initial allocator success to480+encoded.length<2^64, exact copied memory (96-byte
  allocator memory ++384 zeroes ++encoded args), arbitrary payload extraction,
  free-pointer preservation, and constructor entry throughPC44.
- `ConstructorArgumentWords.lean`: generic encoded-word/list read lemmas; all six
  constructor head words and both string length-word reads; head MLOADs in copied
  memory. These are proved for symbolic strings, without size assumptions.
- `ConstructorHeadDecode.lean`: shared canonical-address decoder2643->2662->return,
  and PC44->52->65->84->107->2690. The last PC is the first string decoder invocation.
  Stack at2690 is [672,end,118,480,end,owner,time,morpho,asset], where
  end=480+encoded.length. Memory is constructorArgumentMemory a.
- Constructor.lean now wires all of these; the one remaining sorry is after this
  head decode in the allocation-success branch. Nonpayable and initial allocation
  failure are fully closed. Continue with string decoder2690/2702/2663/2678/2713/
  allocator2608/2727/2742; first return118, then second return150. Source first
  string allocation is the second statement of constructorInputAllocation.

Full verification after the source-prefix change: `.constructor-current-build.log`
passed4503 jobs (Correct + ConstructorSizeWitness). After the copy proof was wired,
`.constructor-copy-build.log` passed4503 jobs. All runtime proofs rebuilt successfully.
Final head-decode assembly verification and initial constructor axiom check are being
run at this checkpoint; record their terminal results below.

Proof lesson: avoid a final `simpa` over generated CODECOPY memory and a theorem that
rewrites a whole encoded buffer. It spent one million heartbeats expanding terms.
First `change` the RD memory and stack to the intended explicit form, then `rw` the
small equalities at that hypothesis. ConstructorReachArgumentMemory now builds in
about3s with default heartbeats. Also wrap `addressWord_val_clean` in an explicit
UInt256.ofNat-typed equality before rewriting (its statement uses EVM.word).

Terminal checks: `.constructor-head-assembly-build.log` passed4505 jobs.
`.constructor-initial-axioms.log` checks bounded deployment, nonpayable,
initial-allocation failure, copied argument memory, and head decoding. Their
dependency counts are4,40,175,186,217, all standard Lean axioms or concrete
native_decide evaluation axioms; no sorryAx or additional trusted dependency.

## Constructor strings, literals, and initial storage (approved-patch continuation)

The constructor now reaches PC434, after both initial empty ERC20 metadata assignments.
Its original single sorry remains at that successful continuation. Both invalid-header
branches and all preceding allocation failures are closed; the 76 runtime proofs remain
complete. Do not treat the old blocked/code-bound notes as current: the bound is approved.

New completed modules after the head decoder:
- ConstructorStringDecode: generic creation string decoder2690 through the allocation
  at2608, payload copy/terminator, and arbitrary return PC. Both allocation outcomes.
- ConstructorStringMemory: encoded name/symbol payload reads, BytesBuffer witnesses,
  cursor/fits arithmetic and preservation through copying.
- ConstructorDecodedBuffers: argumentEnd=480+encoded.length; nameEnd=argumentEnd+32+
  paddedSize name.size; stringsEnd=nameEnd+32+paddedSize symbol.size. Defines the name
  and symbol memories, buffers, free cursor and earlier-window preservation.
- ConstructorPrefixSource: nested cursor frames, initial allocation prefix, generic
  source string/literal allocation calls, and source revert packaging.
- ConstructorStringsRuntime/Source: decode both strings, reach150 with
  [nameEnd,argumentEnd,owner,time,morpho,asset], and close either string allocation failure.
- ConstructorLiteralMemory/Runtime/Source: allocate32,32,32,64; store three empty strings;
  reach229. Success iff stringsEnd+160<2^64. Every partial-allocation failure is matched
  to the source. constructorReadyFrame retains all successive cursor inserts.
- ConstructorLiteralBuffers: all three empty buffers and the version buffer "1" at
  stringsEnd+96; constructorVersionMemory writes length1 and ASCII49<<248.
- ConstructorStorageHeader: version229->260, both old header loads/checks, and panic1824
  for an invalid storage-string header. Slots3/4 are selected by Bool symbol.
- ConstructorStorageSource: unshadowed/resolve/write/revert source facts for both initial
  metadata fields; currently also retains the narrower initial-name revert wrapper.
- ConstructorStorageLoop: generic forward clearing loops2560/2348, writes2574/2362,
  and exits296/392. The account-map recursion is clearDataWordsForwardFrom.
- ConstructorStorageClear: short-header skip and long-header hash/count/clear prefix.
  emptyStringClearedAccounts is generic in the storage slot. Scratch memory writes0
  with slot3/4; hashing uses the proved wordAt0Mem round-trip, no slot-disjointness premise.
- ConstructorStorageWrite: empty packed-header writes317/413 and exact agreement with
  storageStringWriteState; generic storageStringWriteEmpty_accounts.
- ConstructorStorageMemory: scratch writes preserve every allocated byte window and
  free pointer. Symbol buffer check338->356.
- ConstructorStorageInit: combines229->434, both invalid-header/source reverts, source
  continuation from body.drop8 to body.drop10, and post-storage SourceState. On success,
  preserves constructorVersionMemory's bytes from96 upward and returns free=stringsEnd+160.

Main success after ConstructorStorageInit:
- evm5=constructorMetadataState(initState...), i.e. write empty slot3 then empty slot4.
- source frame=constructorReadyFrame a; rest=contract.ctor.body.drop10.
- RD434 stack=constructorMetadataTail a a.stringsEnd true:
  [stringsEnd,stringsEnd+96,owner,morpho,argumentEnd,nameEnd,asset,time,32,64].
- mem5 has a ByteMemoryPrefix from constructorVersionMemory (constructorStringsMemory a)
  a.stringsEnd for every limit; free MLOAD64=ofNat(stringsEnd+160).
- No first-header validity assumption is added: validation branches are proved.

Build checkpoints before the next source correction:
.constructor-strings-assembly-build.log passed4512 jobs;
.constructor-literal-assembly-build.log passed4515 jobs;
.constructor-literal-buffers-build.log passed3640 jobs;
.constructor-storage-header-build.log passed3643 jobs;
.constructor-storage-base-build.log passed3655 jobs;
.constructor-storage-write-build.log passed3669 jobs;
.constructor-storage-memory-build.log passed3670 jobs;
.constructor-storage-init-build.log passed3681 jobs.
.constructor-storage-assembly-check.log passed (the expected original sorry warning).

Next source correction was reported immediately to the user and applied:
- Creation3545 allocates a 36-byte length+selector request (rounded64) before STATICCALL3594.
- The shared raw-return routine3498 checks nonempty return length<2^64 and allocates
  32+paddedSize(return length); empty returns use the shared zero buffer at96.
- ConstructorDecimalsSyntax adds allocatedTryGetAssetDecimalsFunction, based on original
  function44. It reserves36, performs the original raw staticcall, aliases encodedDecimals
  to returndata for reserveCallReturn, then uses allocationBody to preserve the old
  boolean/uint8 result and return the cursor alongside it.
- Spec appends this helper, preserving all existing function indices. ConstructorAllocationSyntax
  uses cursorCall to bind decimalResult and the returned cursor after the first two stores.
- Main source rest atdrop10 is now constructorDecimalsCall (three statements) followed by
  original constructor body.drop4. Earlier drop8/drop4 source proof statements are unchanged.
- ConstructorLiteralSource requires an explicit `change` to literalAllocation ++ body.drop8
  before execBlock_append: the new constructor list association otherwise makes elaboration
  infer the wrong prefix. Both affected proofs were adapted and a leaf check launched.
- Full Correct rebuild is .constructor-initial-storage-build.log; first attempt hit only that
  list-shape elaboration error while other modules continued. Verify terminal result and rebuild
  once the corrected leaf is checked. No runtime semantic audit or differential test was rerun.

New external-call preparation, not yet wired in Main:
- ConstructorCallReturn: shared creation routine3498, empty3540, length2663/2678,
  allocation2608, copy3529. Uses callReturnFits/Pointer/Memory and both failure branches.
  .constructor-call-return-check.log passed; lake build still required.
- SelectorCallMemory: BytesBuffer and ByteMemoryPrefix for allocatedWordCallMemory with
  no ABI arguments. .selector-call-memory-check.log passed; lake build still required.
- ConstructorDecimalsRequest: selector/encode fact,434->3545, and request allocation through
  STATICCALL entry3594 or allocator revert. Draft needs leaf checking after dependencies build.

Proof lessons: source evalExpr? is not reducible by rfl for bytesLit; use
`simp only [evalExpr?, pure]`. Generic constructorMetadataTail length needs explicit simp
unfolding. For slot hashing rewrite uInt256OfByteArray_eq before applying wordAt0Mem_keccak_word;
definitional equality otherwise unfolds the hash and times out. An existential junk stack word
must be explicit before a tactic continuation. uint256_sub_zero_right is the subtraction lemma.


## Constructor decimals and domain progress (2026-10-14)

The user's approved code-size patch remains applied: Constructor uses
`typedConstructorRefinementWithCodeBound`; Correct uses the matching WF capstone.
Do not ask again. All 76 runtime proofs remain complete. The constructor is the
only unfinished leaf. No new assumptions, axioms, sorries, or admits were added.
No differential suite or semantic audit rerun was performed.

The storage checkpoint did finish: `.constructor-initial-storage-build.log`
passed4530 jobs. New helper axiom checks for constructorDecodeSymbol,
constructorLiteralAllocations, constructorStorageInit, and constructorCallReturnBuffer
were clean (standard Lean axioms and concrete native_decide evaluation axioms only).

Completed and built the first external decimals query:
- ConstructorDecimalsRequest: request selector/ABI encoding,434->3545,
  36-byte checked request reservation (rounded64), entry STATICCALL3594.
- ConstructorDecimalsCall:3594->3595 via typedStaticcallSimulation, including the
  call-depth case, typed decimals call bridge, SourceState, and return-size bound.
- ConstructorCallReturn:3498 empty/shared96 or checked return allocation/copy.
- ConstructorDecimalsResult:3602 returns(word,valid), with failure/short/noncanonical
  uint8 branches yielding(word0,false).
- ConstructorDecimalsRuntime combines these routines and both allocation failures.
- ConstructorDecimalsSource/Function prove the added allocated decimals helper's
  body and statement success/reverts; constructorDecimalsValue is tuple(bool,uint256).
- ConstructorZeroMemory: preserves the shared empty buffer at96.
- ConstructorDecimalsInit combines RD434->443, or a matching source/EVM revert;
  source continuation body.drop10->drop13. Cursor is
  callReturnCursor(nextCursor(ofNat(stringsEnd+160))36)out.

Full `.constructor-decimals-assembly-build.log` passed4539 jobs. It included the
following further source correction, reported immediately when identified:
creation479 reserves192 bytes for the EIP-712 preimage, so allocatedConstructor
now inserts reserveBytes192 before the original _buildDomainSeparator call.
The allocation is at body index20. Existing function indices remain unchanged.

Source body indices now:
0 guard;1..7 input/literal allocations;8 empty ERC20 name;9 empty ERC20 symbol;
10..12 allocated optional decimals call;13 underlyingDecimals;14 asset;
15 name;16 version;17 hashedName;18 hashedVersion;19 cachedChainId;
20 domain reserve192;21 buildDomain call;22 cachedDomainSeparator;23 cachedThis;
24 owner nonzero;25 transferOwnership;26 morpho nonzero;27 optional timelock guard;
28 setTimelock;29 vaultName;30 SetName;31 vaultSymbol;32 SetSymbol;33 MORPHO;
34 strict decimals query;35 DECIMALS_OFFSET;36 forceApprove.

Completed constructor domain modules:
- ConstructorUnderlying: optional decimals or18, immutable stores160/128,
  RD443->450->2802 and source body13/14.
- ConstructorShortLiteral: generic creation short-string routine2802 or3174,
  empty/version words. ConstructorDomainLiterals combines it through479.
- ConstructorDomainLiteralMemory and ConstructorAssetInit preserve and encode the
  literals, connect source body13->15, and combine RD443->479.
- ConstructorDomainSource: five constant immutable assignments/name/version hashes.
- ConstructorDomainMemory: generic memLoad_writeWord_disjoint, BytesBuffer.keccak,
  constant-store memory, literal hashes, free-pointer preservation, domain words.
- ConstructorDomainEncode: block479 normalized to the five-word preimage, RD2608.
- ConstructorDomainAllocation: checked192 allocation or revert; RD588, buffer/hash/free facts.
- ConstructorDomainHashSource: source _buildDomainSeparator for a partial immutable store.
- ConstructorDomainReserveSource: constants+allocation source continuation/failure,
  cache helper call+two immutable assignments.
- ConstructorDomainInputs: carry empty/version buffers and free pointer through asset writes.
- ConstructorDomainCache: RD588->616 or zero-owner revert, with exact cached-domain/self memory.
- ConstructorOwnerSource: source owner guard and cache continuation/revert.
- ConstructorDomainInit: combine all domain paths with source body15->25.

Build checkpoints: domain-prefix passed3714 jobs; domain-cache passed3696;
ConstructorOwnerSource built in the first domain-init build (the remaining init
elaboration timeout was subsequently fixed and its direct lake-env check passed).
Main has now been wired through ConstructorDomainInit, leaving its original sorry
at RD616. Full Correct build launched as `.constructor-domain-assembly-build.log`;
check its terminal result before recording success. New helper axiom checks are pending.

At Main's remaining successful branch:
- evm6/hs6 are unchanged since the optional decimals call, accountMap=evm6.accountMap.
- howner: owner nonzero.
- hcursor8: constructorDecimalsCursor.toNat+192 <2^64.
- hdomainSource: source continuation from constructorDomainReadyFrame a ok out I,
  body.drop25, back to constructorAssetReadyFrame a ok out, body.drop15.
- hdomain: RD616, constructorOwnershipTail a =
  [morpho,owner,argumentEnd,nameEnd,asset,initialTimelock,32,64].
- memory=constructorDomainReadyMemory mem6 a ok out I, where mem6 is the decimals
  request/return memory. This includes immutable writes at128/160/352/384/288/320/224,
  allocated domain preimage, and cached domain192/self256.
- hassetSource, hdecimalSource, hstoreSource, hsource compose earlier source prefixes.
- hp5/hp6 still prove preservation of the original literal memory up to stringsEnd+160
  before immutable writes; constructorDomainInputs supplies the literals when needed.

Next bytecode block616 clears pending owner at9, sets owner at8, emits ownership,
then rejects zero morpho (2142) or reaches711. Existing Ownership.lean provides
ownershipState/ownershipAccounts, ownershipBody/Call. Reuse these; no new storage
noncollision assumptions. Bytecode711 tests initialTimelock;716 sets timelock17,
emits SetTimelock, and begins vaultName24 storage. Later vault metadata stores,
strict decimals, DECIMALS_OFFSET, forceApprove, and deployment remain.

Proof-engineering lessons:
- Keep ConstructorArgs.encoded locally irreducible in wrapper routines. Without it,
  defeq unfolded word bytes hundreds of thousands of times; with it AssetInit built2.6s
  at default heartbeats. No heartbeat raise remained.
- Give ptr/mem/ret/data explicitly to constructorShortLiteral; pre-prove load equations.
- UInt256.ofNat0/1 do not rewrite as word literals automatically. Supply closed equalities.
- Normalize generated constant MSTORE offsets to Nat before rewriting named hash facts.
- For complex Frame projections, use simp-only normalization to pre-prove exact typed
  hypotheses. Passing a defeq-equivalent lookup fact directly can unfold the entire
  callable table and time out. DomainReserveSource uses hl' and hcall' for this reason.
- Tuple eval uses evalExprList?; list returns use evalExprs?.
- All new source and runtime modules above are proof-complete; only the original
  Constructor.lean continuation still uses sorry.


## Constructor checkpoint through timelock setup (2026-10-14)

The domain assembly above completed successfully:4556 jobs. Targeted helper axiom
checks passed: constructorDecimalsInit785, constructorAssetInit350,
constructorDomainInit550 dependencies; all standard Lean or concrete native_decide
axioms, no sorryAx or custom assumptions.

Further modules are complete and built:
- ConstructorOwnershipRuntime:616->711, clears pending owner9, sets owner8, emits
  OwnershipTransferred, rejects zero morpho at2142. Exact ownershipAccounts.
- ConstructorOwnershipSource: reuses Ownership.ownershipCall; source continuation
  body25->27 and SourceState.constructorOwnership.
- ConstructorDomainContext: original-argument getter preservation through cursor
  locals; owner/morpho getters, frame contract, cached-memory free pointer.
- ConstructorOwnershipInit: combines the source/EVM paths and SourceState.
- ConstructorTimelockGuard:711->716 or source-matched invalid-timelock revert.
  Zero bypasses bounds; nonzero checks <=1209600 at2091 and >=86400 at2102.
- ConstructorTimelockSource/Init: source conditional body27->28; the checkTime local
  is inserted only on the nonzero branch. No state change.
- ConstructorVaultBuffers: generic BytesBuffer.wordSequence_before, preservation
  through immutable/preimage/cache stores, and both decoded metadata buffers.
- ConstructorSetTimelockRuntime:716->780, sets timelock14, emits SetTimelock using a
  scratch word at the free pointer, clears pendingTimelock17, reads the name length.
  The source already has this exact store order. No spec change was needed.
- ConstructorSetTimelockSource/Init: shared setter call, source body28->29,
  SourceState.constructorSetTimelock, and both preserved BytesBuffers.

Main is now at the original sole sorry, RD780. Full
`.constructor-timelock-assembly-build.log` passed4567 jobs, including Correct.
The constructor is still unfinished; do not mark the goal complete. Targeted
ownership/timelock helper axiom checks were launched in
`.constructor-timelock-axioms.lean` / `.constructor-timelock-axioms.log`.

Current Main success context:
- hs9 relates ownershipState evm6 (ofNat a.owner.val) to ownershipAccounts I ...;
  hownershipSource consumes source body25/26 and resumes body27.
- htime : initialTimelock=0 or86400<=initialTimelock<=1209600.
- htimeSource consumes the optional range check, body27->28.
- hsetTimeSource consumes the setter, body28->29.
- hs11 relates setTimelockState (ownershipState evm6 ownerWord) a.initialTimelock
  to constructorSetTimelockAccounts I (ownershipAccounts I evm6.accountMap ownerWord)
  a.initialTimelock.
- source frame=constructorTimelockReadyFrame a ok out I; nextbody.drop29 is vaultName.
- hname11/hsymbol11 are BytesBuffer proofs in constructorTimelockMemory mem6 a ok out I.
- htimeSet is RD780 with constructorVaultNameTail a:
  [name.size,argumentEnd,nameEnd,asset,morpho,32,64].
- constructorTimelockMemory writes the event word a.initialTimelock at
  constructorDecimalsCursor.toNat+192 in constructorDomainReadyMemory.
- hcursor8 bounds that free pointer by2^64; hlo6 places the prior cursor above
  stringsEnd+160. Source/EVM free pointer is unchanged by this event write.
- Next: validate and write vaultName slot24, emit SetName, then vaultSymbol slot25,
  emit SetSymbol; MORPHO, strict decimals, DECIMALS_OFFSET, forceApprove, deployment.

Useful upcoming reuse: stringViewSlot false/true is24/25, so StringWriteState's
storageStringWriteState_accounts already covers these fields. StringStorageWrite
has generic assignStorageString/assignStorageStringReverts. StringWriteRoutines,
StringClearLoop, StringLongStore, StringStorePrefix etc prove runtime-specific
traces but contain reusable memory/arithmetic/account characterizations.
StringBuffer requires a padded size bound, while BytesBuffer only requires actual
bytes. To reuse StringBuffer word/mask lemmas, derive the padded bound from
constructorTimelockMemory size (it is >=priorCursor+224, past both strings).
Never infer zero initial storage; clearing old long strings and invalid header
branches are still required.

Routine proof notes: use typed local mask equalities before simp when the general
lemma is stated with EVM.word but the goal uses UInt256.ofNat. Likewise give
ult_zero/ult_one a typed word equality before rw when a numeral determines a
metavariable. The local SourceState.constructorOwnership and constructorSetTimelock
lemmas require explicit namespace application, rather than hs.constructorOwnership.
All new modules compile at default heartbeats; no temporary diagnostic settings remain.

## Constructor checkpoint through strict decimals (2026-10-14)

The approved code-size-bound patch remains applied in Constructor/Correct. Do not
ask for it again. The original sole constructor sorry is now at PC1053, source
body.drop36, immediately before DECIMALS_OFFSET and forceApprove. Runtime remains
complete. Correct itself rebuilt successfully after the new source allocation
accounting; a combined build also included the new approval ABI helper, which is
being checked separately. Do not claim the constructor or goal is complete.

Vault metadata is now fully proved, including arbitrary initial storage:
- ConstructorVaultHeader/ClearLoop/ClearDispatch/ClearStart/Clear validate old
  storage headers and clear obsolete long-string words.
- ConstructorVaultTopicMemory/DataLoop/ShortPrefix/LongTail/Store/Write cover
  short/long data, exact account updates, event-topic loading, and scratch memory.
- ConstructorVaultSource/AssignInit/StringBuffers/NameInit couple the name store
  to the source and preserve both decoded string buffers.
- ConstructorStringEncoder/VaultEncode/VaultEventSource/NameEvent/SymbolInit
  encode and emit the name, store the symbol, and encode its event through PC1010.
- ConstructorMorphoRequest emits SetSymbol, writes MORPHO at416, encodes the strict
  selector, and shares the actual STATICCALL1039 with the source.
- ConstructorMorphoSource/Context assign MORPHO and retain arguments/cursor.
- ConstructorStrictDecimalsABI/Allocation/Source/Memory/Init cover call failure,
  capped32 return allocation, short returns, noncanonical uint8, source reverts,
  memory preservation, and continuation at1053.

Reported and corrected source-model omission: strict decimals must reserve32 on
a successful canonical return. ForceApprove allocates100 for its original request
and another100 only for fallback approve(0); the final fallback approval reuses
the original request. Every low-level call reserves nonempty raw returndata before
inspecting success. ForceApproveAllocationSyntax appends allocatedOptionalReturnBoolFunction
and allocatedForceApproveFunction to Spec.functions (existing indices unchanged).
The original helpers are functions75 and46 respectively. ConstructorAllocationSyntax
now inserts reserve32 at35, leaving earlier source indices unchanged. Body36 is
DECIMALS_OFFSET; body37..39 is cursorCall to allocatedForceApproveFunction.
The original Solidity, bytecode, and generated block summaries were not changed.

Builds through name and symbol previously passed4585/4590 jobs. New strict helper
build passed3788 and strict Init passed3790. Main compiles through1053. The full
post-spec-change build compiled every runtime proof and Correct (4601 jobs in the
combined invocation); inspect `.constructor-strict-assembly-build.log` for the
latest combined result, including the approval ABI helper.

Targeted new-helper axiom checks in `.constructor-vault-strict-axioms.log` passed:
VaultNameInit2351, VaultNameEvent227, VaultSymbolInit2528, StrictDecimalsInit587.
Only standard Lean and concrete native_decide axioms; no sorryAx or new assumptions.
Earlier ownership/timelock checks also passed (337/161/80 dependencies).
No differential tests or runtime semantic/axiom audit reruns were performed.

Main success context at the remaining sorry:
- evm15/out15 come from the strict STATICCALL; hs15 is SourceState.
- hlong15:32<=out15.size; hout15:out15.size<2^138; hdecimals15:word0<256.
- halloc15: allocationFits (constructorStrictDecimalsPtr a out)32.
- constructorStrictDecimalsPtr a out = ofNat(optional-decimals cursor.toNat+192).
- hstrictSource consumes sourcebody32..35 and resumes body36 in
  constructorFinalDecimalsFrame a ok out I out15.
- hstrict is RD1053 [255,word0,asset,morpho,32,64], memory
  constructorFinalDecimalsMemory mem14 a out out15, accounts evm15.accountMap.
- That memory writes MORPHO416 and the selector at the old free pointer, copies
  min(32,out15.size), then writes free64 = nextCursor oldFree32.
- hs14 related the state after name24 and symbol25 storage updates; hm14>=96.
- hp12 preserves all byte prefixes from timelock memory to name-store memory;
  hp13 preserves below oldFree through the name event; hp14 preserves below
  oldFree through the symbol store/event encoding. Compose these when recovering
  immutable memory slots128..384. MorphoMemory_prefix preserves below416;
  MorphoMemory_morpho gives416; StrictDecimalsMemory_prefix preserves belowoldFree.
- Source failure composition now additionally uses hsymbolSource and the name
  event prefix, followed by hnameSource, hsetTimeSource, htimeSource,
  hownershipSource, hdomainSource, hassetSource, hdecimalSource, hstoreSource, hsource.

Next helpers already written: ConstructorDecimalsOffset (proved and built) models
the uint8 offset as ofNat(18-word0.toNat), with source assignment prefix36->37 and
the exact masked EVM formula. ConstructorApproveABI encodes approve(address,uint256)
and its BytesBuffer; its latest build is pending in the log above.

Next bytecode:1053 writes offset448 and the approval payload at free+32, then calls
allocator2608 for100, ret1119.1119 reaches CALL1126.1127 invokes the existing
constructorCallReturnBuffer at3498, ret1134. Success/optional-bool/code checks lead
to1153 (deployment) or1420 (fallback).1420 allocates another100,1469 calls3692 for
approve(0),1475 calls3692 again using the original request,1480 reaches1153.
Deployment1153/1251/1343 copies19708 runtime bytes from creation offset3894 and
patches all immutable sites. Read generated summaries before implementing traces.

Proof notes: use explicit `words := [...]` with allocatedWordCallMemory_read;
rw cannot infer the sequence from literal length68. Use `simp` for fixed-list stack
bounds containing variables (`decide` refuses free variables even with +kernel).
ofNat_add_words rewrites sums of words to ofNat(sum), so use its reverse for the
other direction. UInt256.mul requires u256_mul_toNat, not the `*` lemma umul_toNat.
Normalize Int.ofNat with Int.ofNat_eq_natCast before omega. No heartbeat raises
were needed for these helpers.
