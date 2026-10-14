# MetaMorphoV1_1 earlier proof history

Archived from HANDOFF.md to keep files below 2000 lines. Compiler provenance and current
status remain in [HANDOFF.md](HANDOFF.md).

## Proof valuation issue found on 2026-10-08

The randomized differential suite was rerun with `--only MetaMorphoV1_1 --count 50` and exited
successfully: both targets again reported 4025 agreements, with zero disagreements or stuck
cases. Those targets use fitting immutable stores.

The generated `MetaMorphoV1_1Immutables` structure represents `_underlyingDecimals` and
`DECIMALS_OFFSET`, both declared uint8, as unrestricted `EVM.Word` fields. Consequently,
`metaMorphoV1_1Correct` and `metaMorphoV1_1DECIMALS_OFFSETBody` quantify over invalid valuations.
At `DECIMALS_OFFSET = 256`, the runtime masks the value with 255 and returns zero, but the
source returns 256, which cannot be ABI-encoded at the declared uint8 return type.

`ImmutableTypeRegression.lean` preserves the executable reproduction and two kernel-checked
facts about the mask and failed return encoding. Both theorem axiom audits contain only
standard Lean axioms. Its module build and executable run pass, with this output:

```text
DECIMALS_OFFSET=255: agree (success)
EVM return word: 255
DECIMALS_OFFSET=256: DISAGREE: the returned values do not ABI-encode at the declared return types
EVM return word: 0
```

The approved correction adds proof fields for `_underlyingDecimals.toNat < 256` and
`DECIMALS_OFFSET.toNat < 256` to the valuation structure, deriving these bounds from
`immutablesFit` in `restrictImmutables_of_fit`. This preserves the final
`metaMorphoV1_1ContractCorrect` statement and the scope of all fitting immutable stores; it
does not require any specification, bytecode, generated block-summary, or Solidity changes.
The user approved this valuation change on 2026-10-08. The bridge is now proved from
`immutablesFit`; its axiom audit contains only `propext` and `Quot.sound`.

Completed functions: `DECIMALS_OFFSET`, `MORPHO`, `asset`, `lostAssets`, `lastTotalAssets`,
`timelock`, `curator`, `guardian`, `skimRecipient`, `owner`, `pendingOwner`, `totalSupply`,
`fee`, `feeRecipient`, `supplyQueueLength`, `withdrawQueueLength`, `decimals`,
`pendingTimelock`, `pendingGuardian`, `balanceOf`, `nonces`, `isAllocator`, `pendingCap`,
`config`, `allowance`, `supplyQueue`, `withdrawQueue`, `setCurator`, `setSkimRecipient`,
`transferOwnership`, `acceptOwnership`, and `renounceOwnership`.

Every completed function covers successful execution, nonzero callvalue rejection, and
oversized calldata rejection. The queue getters cover bounds failures; the setters cover
authorization, unchanged-value rejection, and static-call halts. The ownership functions cover
authorization and static-call halts, preserving the unused portions of packed storage slots.
`decimals` also covers uint8 sum overflow. All thirty-two individual axiom audits contain only
standard Lean axioms and permitted concrete evaluation axioms; none contains `sorryAx`.
The full `Correct` target passed at the thirty-two-function checkpoint (3619 jobs).
There are **45 remaining placeholders** in other functions and the constructor. This is an
intermediate checkpoint, not a completed correctness proof.

Logs include `/tmp/metamorpho-32-functions-build.log`,
`/tmp/metamorpho-transfer-ownership-build.log`, and `/tmp/metamorpho-accept-ownership-build.log`.

The next dependency chain is `_maxDeposit` and the market/share arithmetic helpers used by
`maxDeposit` and `maxMint`; these functions are not constant limit getters in this specification.

The following dependencies now have completed proofs (the ABI-function count is unchanged):

- `Arithmetic`, `CheckedArithmetic`, `MarketArithmetic`, and `MulDiv`: source arithmetic and
  shared EVM checked addition, multiplication, division, and zero-floor subtraction routines.
- `SharesToAssetsUp` and `SharesToAssetsUpRoutines`: rounded-up share-to-asset conversion,
  including all arithmetic failure branches, on both the source and EVM sides.
- `PackedSource`, `MorphoSlots`, and `MemoryArraySource`: source packed encoding, casts, nested
  storage-slot hashes, and the singleton array used by `MorphoLib_supplyShares`.
- `MemoryRoutines`, `MemoryArrayData`, `MemoryArrayRoutines`, and `PackedHashMemory`: allocation,
  first-element access, singleton memory contents, and two-word hash buffers. The memory proofs
  establish the length, contents, free cursor, and preservation of earlier allocated words.
- `MorphoSlotRoutines.supplySharesReachEncoding`: EVM execution from pc 14078 through the nested
  hashes and singleton construction to pc 14169. It assumes the explicit allocation bound
  `ptr.toNat + 256 < 2^64`; callers must discharge it. Its audit contains 152 allowed axioms,
  including concrete evaluation facts, and no `sorryAx` or unexpected axioms.
- `SupplySharesSource`: the source supply-share reader, parameterized by the actual typed
  `extSloads` call. It covers a nonempty decoded array, call failure, decoding failure, and an
  empty decoded array.
- `ExtSloadsABI`, `ExtSloadsMemory`, `ExtSloadsEncode`, and `ExtSloadsSetup`: the exact 100-byte
  singleton request, preservation of its input array, the encoding loop, and the input stack
  at STATICCALL pc 14210.
- `ExtSloadsCall.extSloadsStaticcall`: couples the actual EVM call witness to the source call,
  including the depth-limit branch, and reaches pc 14211. Its audit contains only the three
  standard axioms and three permitted concrete evaluation axioms.

Recent successful dependency build logs include `/tmp/metamorpho-slot-routines-build.log`,
`/tmp/metamorpho-memory-array-routines-build.log`, `/tmp/metamorpho-slots-hash-memory-build.log`,
`/tmp/metamorpho-extsloads-setup-build.log`, and `/tmp/metamorpho-extsloads-call-build.log`.

## New unresolved return-buffer allocation mismatch

Do not continue ordinary function proofs until this issue is resolved, as required by
`Misc/prompt.md`. The previous approval concerned the uint8 immutable bounds; it did not
authorize changing the source semantics outside this benchmark or restricting the gas domain.

`ExtSloadsAllocationRegression.lean` contains a symbolic buffer of exactly `2^64` bytes:
the ABI offset is 32, the array length is one, and all remaining bytes are zero. It proves:

- `oversizedReturn_sourceAccepts`: the current external ABI decoder accepts a one-element array.
- `oversizedReturn_allocatorRejects`: with free cursor 512, the compiled allocation guard fails.
- `oversizedReturn_evmReverts`: from a successful-call state at pc 14211 with that buffer, the
  supplied block summaries reach the allocation panic at pc 2690 and prove `RDrev`.
- `oversizedReturn_withinGasDerivedBound`: the buffer is within the existing proved bound for
  opaque EVM return data.
- `oversizedReturn_memoryGasFits`: its EVM memory expansion costs less than `2^120` gas, a budget
  allowed by the current 256-bit gas domain.

These are checked local boundary facts, **not** an end-to-end counterexample to `Correct`.
In particular, no complete transaction or callee `Theta` reachability witness is asserted.
The source-acceptance proof uses only standard Lean axioms. The conditional bytecode-revert
proof uses 74 allowed axioms, including concrete bytecode facts, with no unexpected axioms.

The source frame does not track a compiler memory cursor. `ABI.decodeReturnValues?` checks
the signed total-size bound and the individual uint64 offset/length bounds, but not the
compiler's cumulative allocation bound. The source also does not reserve the copied return
buffer. Thus decoder well-formedness alone cannot discharge the allocator guard. The earlier
explicit `ptr + 256 < 2^64` obligation also requires a cumulative memory invariant at callers.

The recommended repair is to retain the unconditional theorem and explicitly model allocation
failure: add a memory cursor and allocation operation to Stele, propagate the cursor across
internal calls, and annotate the benchmark's compiler allocation sites, including the raw
return-buffer copy and decoded array. Likely library changes would involve
`Stele/Semantics/Types.lean`, `Stele/Syntax/Basic.lean`, `Stele/Semantics/Exec.lean`, the interpreter
and syntax support, and the affected `Reasoning` combinators. This exceeds the current
benchmark-only edit scope and needs a scope decision before implementation. A smaller gas
domain is an alternative change to the theorem's claim, not an implicit assumption we may add.

Regression build log: `/tmp/metamorpho-extsloads-allocation-regression-build.log`.

## Resumption on 2026-10-09: external-call reachability established

The saved `ExtSloadsOversizedCallee.lean` trace typechecks. It executes a concrete 21-byte
callee from its initial state and returns `oversizedReturn` using `2^120` gas. The buffer
remains symbolic: no test attempts to allocate `2^64` bytes.

This resumption extended that file with the following checked facts:

- `oversizedCalleeTheta` proves a successful `Theta` invocation of the callee installed at
  address `0x6000`, called from `0x6001`, with zero value and static permissions.
- `oversizedCalleeTypedCall` supplies the same witness to `typedCallViaEVM` for the actual
  `extSloads` singleton request, for every requested slot.
- `oversizedCalleeCallAccepted` combines that call with the existing ABI-decoder proof: the
  decoder accepts a one-element array from an output of size exactly `2^64`.
- `acceptedCallDoesNotBoundReturnSize` refutes the proposed general implication from
  successful typed calls and accepted array decoding to `out.size < 2^64`.

These results close the callee-reachability gap in the earlier boundary evidence. They do
**not** assert an end-to-end vault transaction counterexample or refute `Correct`: the vault's
post-call state in `oversizedReturn_evmReverts` is still a hypothesis. In addition, Stele's
external-call relation existentially quantifies the callee gas, so a boundary discrepancy
alone is insufficient to refute the existential top-level refinement. Replacing the actual
successful call with a different failing call would not satisfy the requested same-call proof
discipline.

The focused `ExtSloadsOversizedCallee` module build passes. No differential suite or previous
audit was rerun. No specification, theorem signature, bytecode, generated summary, or shared
library was changed, and no placeholder or assumption was added. The 45 existing placeholders
remain.

The allocation-model repair remains unresolved. A benchmark-local alternative to shared
Stele changes is explicit cursor passing through internal helper arguments and results, with
raw return-buffer reservation and decoded-value allocation checks at the compiled sites.
That requires updating the affected source helpers and their proofs, not merely adding a
fixed output-size check. The user has been asked to choose between that local rewrite and an
explicit scope expansion for shared Stele memory accounting. Keep the directory restriction
in force unless the user changes it.

## Local allocation repair: checked helpers and complete supply-share routine

The benchmark-local cursor-passing repair is now underway within the existing directory
restriction. No shared Stele or Reasoning source has been edited. The earlier scope question
does not prevent this local work; there is no authorization to expand the edit scope.

`Spec.lean` now appends three internal helpers, preserving every original function index:
`__solcAllocateMemory`, `__solcExtSloads`, and `__solcMorphoSupplyShares`. Their syntax is in
`AllocationSyntax.lean`, `ExtSloadsAllocationSyntax.lean`, and
`SupplySharesAllocationSyntax.lean`. The original source readers and their upstream callers
have **not yet** been redirected or given cursor arguments/results. Thus this is a modular
repair in progress, not a completed repair of the top-level specification.

Checked new results:

- `AllocationSource.lean` / `AllocationRoutines.lean`: exact source and bytecode allocator
  success/failure, including rounding and wraparound, without an assumed allocation bound.
- `ExtSloadsSimulation.extSloadsPostCallSimulation`: all post-call paths from pc 14211
  through raw-buffer reservation, dynamic-array decoding/allocation/copy, to pc 14256 or
  `RDrev`. It uses the same actual call witness and derives the return-size bound from it.
  The component files cover malformed headers, missing payload, and both allocation failures.
- `ExtSloadsAllocationRepair.oversizedReturn_repairedSourceReverts`: the registered helper
  reverts for the actual successful oversized callee witness at cursor 512. This remains a
  helper-level regression, not a top-level transaction counterexample.
- `MorphoSlotAllocation.lean`: the supply-share prefix covers failure at either 96-byte hash
  allocation or the 64-byte singleton-array allocation; success reserves 256 bytes total.
- `SupplySharesAllocationSource.lean`: complete source execution of the registered
  cursor-aware reader, including allocation failure, external-helper failure, empty array,
  and successful `(value, cursor)` return.
- `SupplySharesAllocationRoutines.supplySharesAllocationSimulation`: complete internal
  routine simulation from pc 14078 through the actual STATICCALL and back to an arbitrary
  valid caller continuation, or paired source/EVM revert. Success returns the matching
  cursor at memory slot 64, with its lower/upper bound and memory-size invariant. The only
  cursor input restriction is the ordinary lower bound 96; allocation fits are case splits,
  not assumptions. `SourceState` is carried across the same call.

Focused builds for the new supply-share routine pass (log
`/tmp/metamorpho-supply-shares-simulation-build.log`). The existing `Correct` scaffold also
built after the first two helpers were registered; registering the third helper has been
validated by focused builds, but a new full `Correct` build is not yet run. The 45 original
placeholders remain, and no new placeholder or axiom has been introduced. No differential
suite or previous audit was rerun.

Next: thread cursor results through the actual source call graph and account for other
compiled allocations in those callers. Do not reset the cursor at each internal call, use a
fixed return-size restriction, or replace the actual successful call by a different failed
call. `SupplySharesAllocationSetup.lean` links its fixed prefix to calldata construction;
`ExtSloadsValueRoutines.lean` proves the empty/nonempty array continuation. Caller proofs
that retain allocated memory will additionally need prefix-preservation facts; the present
routine theorem exposes the cursor invariant but does not yet return `MemoryPrefix`.

## Cursor propagation and complete market-parameter reader

The preceding registration/root-status paragraph is superseded. `Spec.lean` now appends six
helpers, adding `__solcMarketParams`, `__solcExpectedMarketBalances`, and `__solcMaxDeposit`.
`MaxDepositAllocationSyntax.lean` threads the cursor through the three reader calls and the
`_maxDeposit` loop. The actual `maxDeposit` transition (index 19) initializes the cursor to
128 and returns the result component. Its original three prefix statements, including both
the nonpayable check and calldata-length check, are preserved. All original function indices
are preserved. Other roots, including `maxMint`, still use their original call chains; the
whole-contract allocation repair is incomplete. `Common.lean` only needs the new transition
definition in the selector-signature simplification. The full existing `Correct` scaffold
built after this integration (log `/tmp/metamorpho-max-deposit-cursor-build.log`).

The compiler's `_marketParams` reader now has a complete, checked internal simulation:
`MarketParamsAllocationRoutines.marketParamsAllocationSimulation`. It begins at pc 16116,
shares the actual STATICCALL witness with the source, and returns to any valid continuation
or produces paired source/EVM reverts. It covers the initial 160-byte zero-struct reservation,
failed calls, short returns, both subsequent 160-byte reservations, and rejection of each
noncanonical address. Success supplies the exact five field words, source struct value,
`SourceState`, and the bounded cursor at memory slot 64. Allocation fits and valid decoding
are conclusions of the case split, not assumptions on callees.

Components: `MarketParamsAllocationSource.lean` (complete source execution),
`StructAllocationRoutines.lean` (the fixed allocator), `MarketParamsCallMemory.lean` and
`MarketParamsAllocationSetup.lean` (initial memory and call setup), `MarketParamsCall.lean`
(same-call correspondence), `MarketParamsABI.lean` (exact ABI success/failure conditions),
`MarketParamsReturnAllocation.lean` (post-call allocations and size guard),
`MarketParamsReturnMemory.lean` (buffer and field-memory facts), and
`MarketParamsDecodeRoutines.lean` (address checks and field stores). Focused build passes:
`/tmp/metamorpho-market-params-simulation-build.log`.

Next dependency is `__solcExpectedMarketBalances`: its syntax reserves 384 bytes after the
`market` call (192-byte return buffer plus 192-byte decoded struct), and 32 bytes after the
conditional `borrowRateView` call. Its source execution, EVM simulation, interest arithmetic,
and the eventual maxDeposit loop remain to prove. Existing `MarketArithmetic.lean` covers
only zero-floor subtraction, not interest accrual. Both completed reader simulations will
need additional `MemoryPrefix` output for callers retaining previously allocated objects.

The 45 original placeholders remain. No new placeholder or assumption was introduced. No
differential suite or previous audit was rerun, and no file outside this benchmark was edited.

## Market-call prefix and six-field decoder

`MarketReadSimulation.marketReadSimulation` now covers the balance reader from pc 16911
through the actual `market` STATICCALL, both 192-byte reservations, six `uint128` field
checks, and pc 16966. Every failed call, short/malformed return, or allocation failure has
a matching source/EVM revert. Success carries the actual source call, `SourceState`, exact
field words, cursor at memory slot 64, and `MemoryPrefix` below the incoming cursor. The
remaining elapsed-time and interest-accrual computation is **not** included in this theorem.

Source components: `MarketParamsHashSource.lean` proves the five-word market identifier
hash and its internal call; `MarketBalancesAllocationSource.lean` proves source execution
through the market call and the 384-byte reservation. `MarketABI.lean` characterizes all six
uint128 checks. Runtime components: `MarketCallMemory.lean`, `MarketCall.lean`,
`MarketReturnAllocation.lean`, `MarketReturnMemory.lean`, and `MarketDecodeRoutines.lean`.
`StructAllocationRoutines.lean` now includes the 192-byte allocator and a general aligned
reservation-splitting fact.

Reusable local helpers were factored into `ScalarTupleABI.lean`, `SingleWordCallMemory.lean`,
`StaticCallSimulation.lean`, and `StructReturnMemory.lean`. Both reader families use them;
the existing market-parameter simulation still builds after these refactorings. Focused
combined build passed in `/tmp/metamorpho-market-read-simulation-build.log`. `git diff --check`
passed. No differential suite or prior audit was rerun; the 45 original placeholders remain.

Next: checked timestamp subtraction at pc 12234, then the short-circuit tests at 16991,
17001, 17007 (helpers 17600 and 17578). No-accrual returns through 17012. Accrual enters
17069, encodes `borrowRateView` through 12112/17114/17198, calls at 17225, reserves 32 bytes
on return through 17524, then computes Taylor terms, interest, and optional fees. Read exact
generated summaries before composing these paths. The older supply-share and market-parameter
whole-routine interfaces still need memory-prefix outputs for callers retaining allocations.

## Elapsed time, allocating casts, and the complete rate call

`MarketBalancesSource.lean` and `MarketBalancesRoutines.lean` now cover checked timestamp
subtraction, the three short-circuit accrual tests, time-underflow rejection, and the
no-accrual return. The full source no-accrual/time-underflow paths are proved; their final
composition with the existing market-read simulation remains. `CheckedArithmetic.lean`
now includes the shared checked subtraction routine at pc 12234.

Important compiler allocation discovered and reported: `UtilsLib_toUint128` at pc 19367
unconditionally reserves 64 bytes for its error string, even on successful casts. The
authorized cursor repair now appends a seventh helper, `allocatedToUint128Function`, and
`allocatedMarketBalancesFunction` routes its three possible casts through it. The new
helper is appended last, preserving earlier helper indices. `Uint128AllocationSource.lean`
and `Uint128AllocationRoutines.lean` prove the source calls and all bytecode outcomes:
allocation failure, value overflow, and success with the advanced cursor, sufficient memory,
and preserved earlier allocations. This is not a new input bound or assumption.

`BorrowRateSimulation.borrowRateSimulation` is now checked from pc 17069 through pc 17239.
It constructs the exact 356-byte request, shares the actual `borrowRateView` STATICCALL
result with the source (including the depth-limit branch), rejects failed calls and short
returns, and handles the 32-byte allocation. Success supplies the decoded rate, SourceState,
cursor, memory prefix, and a source continuation through the call/reservation. Components:
`BorrowRateABI`, `BorrowRateCall`, `BorrowRateSetup`, `BorrowRateReturn`, `BorrowRateSource`,
`BorrowRateReadMemory`, and `BorrowRateEncodeMemory`. `MarketParamsEncode.lean` proves the
shared five-field encoder at pc 12112. `WordCallMemory.lean` and `wordWindowPrefix_load` are
reusable local memory helpers. Focused builds passed for these components; the simulation
build log is `/tmp/metamorpho-borrow-rate-simulation-build.log`.

Next is the Taylor expansion and interest arithmetic. Source function 79 computes
first=x*n, second=mulDivDown(first,first,2e18), third=mulDivDown(second,first,3e18), and
checked `(first+second)+third`. Bytecode: checked multiply 12002 returns first at 17278;
17278 squares first, returning 17300; 17300 divides by 2e18 and multiplies second*first,
returning 17320; 17320 divides by 3e18 and calls checked add 12077 with return 17327;
17327 calls checked add again, with caller-supplied return (17332 in this path). 17332
then swaps into checked multiplication for interest, returning 17338; that divides by
1e18 and enters the allocating cast at 19367. Read exact summaries for stack details.
`WadMultiply.lean` and the added mulDivDown call wrappers already prove source multiplication.

The 45 original placeholders still remain. No original audit or differential suite was
rerun, no assumption was added, and edits remain within this benchmark. `git diff --check`
passed at this milestone. Overall cursor repair still affects only maxDeposit; other roots
need repair before their proofs can be completed.

## Taylor and interest arithmetic

`TaylorWords.lean`, `TaylorSource.lean`, and `TaylorRoutines.lean` now prove the full
Taylor helper, including every checked-multiplication failure. `taylorSumsFit` derives
both final-addition bounds from the already checked square, so the proof adds no input
assumption. The focused Taylor build passed in `/tmp/metamorpho-taylor-routines-build.log`.
`MarketInterestSource.lean` and `MarketInterestRoutines.lean` pair the two source calls
with pc 17239 through the first cast at pc 19367, including Taylor and interest-product
overflow. `Uint128Add.lean` proves the checked narrow source addition and the compiler
routine at pc 16879, for success and panic. Their combined focused build is recorded in
`/tmp/metamorpho-market-interest-routines-build.log`.

Next compose the two 64-byte allocating casts and the borrow/supply asset updates,
then the optional fee branch. The cast return pc 17353 is shared by the borrow-assets
and fee-shares additions. The second interest cast returns to pc 17378. These routines
must retain the market's memory loads through the allocations and stores.

## Asset updates and fee branch

`MarketAssetsSource.lean` proves the two allocating casts and checked borrow/supply asset
updates, on success and every failure. `MarketAssetsRoutines.lean` pairs these with bytecode
pc 19367 through pc 17387 (before the final supply store). `MarketAssetsMemory.lean` proves
the memory effects after that store: both changed fields, preservation of disjoint fields,
free cursor, size, and the prefix below the market struct. Supporting reusable local files:
`CursorCastSource`, `CastFieldSource`, `CastAddFieldRoutines`, `CastStoreMemory`, and
`MarketValueUpdates`. Focused builds passed; see `/tmp/metamorpho-market-assets-routines-build.log`
and `/tmp/metamorpho-market-assets-memory-build.log`.

`SharesDownSource.lean` proves function 81 for canonical uint128 market totals (including
product overflow). These internal bounds come from decoded/updated market fields.
`MarketFeeSource.lean` proves the entire fee body, including subtraction underflow,
share-product overflow, allocation/cast failure, and checked share-total overflow.
`MarketFeeArithmetic.lean` covers pc 17400 to 19367; `MarketFeeRoutines.lean` pairs the complete
fee source body with pc 17400 to 17012, using the same value and cursor. Success memory is
`castStoreMemory` at the shares field. Build logs:
`/tmp/metamorpho-market-fee-arithmetic-build.log`, `/tmp/metamorpho-market-fee-routines-build.log`.

`MarketBalanceFinal.lean` now checks the pc 17387 supply store and fee/no-fee branch, plus
a generic four-word uint128 return routine at pc 17012 with arbitrary returndata (the rate
call has replaced the original market returndata). It also proves source returns for updated
market values. Composition of asset updates, fee selection, optional fees, and final return
is next; then prepend interest and the already proved rate/market external-call simulations.
The 45 original placeholders remain. No old audit or differential suite was rerun.

## Complete market-balance helper

`MarketBalancesSimulation.marketBalancesSimulation` is now checked and built. It starts
at pc 16911 with the Morpho address, market-parameter pointer, and return address, and
pairs the full source helper with either EVM revert or the final four-word return. It covers
the actual `market` call, decoding and allocation, timestamp underflow, skipped accrual,
the actual rate-model call, Taylor/interest arithmetic, both asset casts/updates, optional
fees, and the final return. Success includes SourceState, all four returned values, the
current cursor and its bounds, sufficient memory, and preservation below the entry cursor.
Build passed: `/tmp/metamorpho-market-balances-simulation-build.log`.

Composition modules: `AccruedBalanceSimulation` (pc 19367 through assets/fees/return),
`InterestBalanceSimulation` (pc 17239 through return), and `MarketAccrualSimulation`
(pc 17069, actual rate call through return). `BalanceSnapshot` in
`AccruedBalanceSimulation.lean` packages final memory/frame, three updated totals, cursor,
and prefix; its `rebase` method composes prefixes. Borrow shares stay the original word96.
`WordWindow.lean` proves that aligned field loads determine the complete byte window and
therefore arbitrary 32-byte loads. This bridges the six field loads from the market decoder
to the call encoder's existing window interface.

Next: integrate the complete reader into `_maxDeposit`'s loop. Input memory to the balance
helper needs the 160-byte market-parameter window and `MarketParamsLoads`; the existing
market-parameter simulation returns `marketParamsReadMemory`, whose field/window properties
can supply these. The existing supply-share and market-parameter readers do not yet expose
memory-prefix results, but maxDeposit mostly retains scalar stack values between calls;
check whether the new caller actually needs these before extending them.

Elaboration lesson: explicitly `dsimp only` frame-update definitions when proving
`frameA.contract = contract`. Definitional unification otherwise unfolds the entire contract
and times out. Keep `wordWindowRead_of_fields (count := 6)` explicit: solving `32 * ?count = 192`
by definitional unification also times out. No heartbeat increases were retained.

## Completed public maxDeposit

`metaMorphoV1_1MaxDepositBody` is proved without placeholders. Focused build passed:
`/tmp/metamorpho-max-deposit-build.log`. There are now 44 original placeholders left.
The theorem includes entry guards, all address-decoding failures, the complete allocated
internal function and queue loop, actual external calls, arithmetic failures, and the final
scalar return. `MaxDepositEntry` and `MaxDepositBodySource` supply the public boundary;
the final connection uses `RDret.reEquivExecutionGen` with the actual final account map.

New composition modules: `MarketParamsDecoded`, `CursorCallSource`, `AllocatedReaderCalls`,
`MaxDepositReadersSource`, `MaxDepositReadersSimulation`, `MaxDepositArithmeticSource`,
`MaxDepositArithmeticSimulation`, `MaxDepositLoopSyntax`, `MaxDepositQueueSource`,
`MaxDepositQueueRoutines`, `MaxDepositInvariant`, `MaxDepositIteration`, `MaxDepositLoop`,
and `MaxDepositFunction`. The three reader simulations now expose storage preservation;
the parameter reader additionally exposes its struct's lower bound and end-before-cursor
bound. These facts are derived, not assumptions. The loop induction uses remaining queue
length; static-call storage preservation keeps the cached length equal to storage slot 20.

Next is `maxMint`, whose bytecode first calls the already proved maxDeposit helper and then
the accrued-fee/assets calculation and conversion. Extend the previously authorized cursor
model through expectedSupplyAssets (function 51), accruedFeeAndAssets (29), convertToShares
(22), and public transition 59. The other public roots still use the original helpers.
ExpectedSupplyAssets retains market parameters in memory across the supply-share read, so
the supply-share simulation will need to expose memory-prefix preservation as well as its
cursor and storage facts. Its current success witness uses concrete call/buffer/array memory.

Public maxMint entry PCs: 2173 nonpayable, 2179 length, 2191 address decoder call, 2198 calls
13894 with stack `[2215, 2234, 1578, 32] ++ R`. PC 2215 calls accruedFeeAndAssets at 12247;
2223 reads totalSupply slot 2 and calls checked add at 12077; 2234 enters conversion at 14489.
No differential suite or prior audit was rerun.

## maxMint readers and accrued-assets loop

The authorized cursor model now extends through public transition 59 (`maxMint`).
`MaxMintAllocationSyntax` appends expectedSupplyAssets (original function 51),
accruedFeeAndAssets (29), and convertToShares (22), bringing the helper list to ten.
`Common.maxMintSelectorOf` unfolds the new transition; no original theorem signatures changed.
The extension was reported when made. Other public roots remain as before.

`SupplyAssetsSimulation.supplyAssetsSimulation` is complete and built. Entry 12483 retains
three caller words plus the Morpho word, performs supply-share reading, market balance
calculation, then conversion to assets rounding down, and returns to an arbitrary valid PC.
It exposes the actual final state, storage preservation, cursor, and memory bounds.
The supply-share allocation simulation now additionally exposes preservation below the
entry cursor and cursor monotonicity. `SupplySharesMemoryPrefix` and `HeapWordWindow`
justify retaining the market-parameter memory window across that read.
`SharesToAssetsDown` and `SharesToAssetsDownRoutines` cover the source and PC 18378 routine.
The combined build also rechecked public maxDeposit successfully:
`/tmp/metamorpho-supply-assets-simulation-build.log`.

`AccruedAssetsIteration` and `AccruedAssetsLoop` are complete and built. The induction runs
from PC 12288 to 12296, preserves storage and the later fee-calculation locals, and covers
every actual external-call, allocation, and checked-add revert. `AccruedAssetsPrefix`
connects function entry 12247 and the initial five source statements to that loop. Success
exposes a source continuation from body.drop 5 and `AccruedAssetsTailLocals`.

`AccruedAssetsTotals` proves the source loss adjustment, checked total-assets addition,
and interest subtraction. `AccruedAssetsTotalsRoutines` covers the same bytecode through
PC 12353, with all failure cases. `AccruedFeeGuard` proves the short-circuit condition:
no fee returns to the caller with stack `[newLost, newTotal, feeShares] ++ R`; a fee reaches
12369 with `[interest, ret, newLost, newTotal, feeShares] ++ R`.
These modules have passed focused builds (logs `/tmp/metamorpho-accrued-*-build.log`).
The most recent edits only wrap long lines in these files and SupplyAssetsSimulation.

Next dependency is OpenZeppelin full-precision mulDiv. The source function 66 uses an
unbounded integer product followed by division and a uint256 range check. The specialized
denominator 1e18 EVM routine starts at 16398; generic mulDiv starts at 16544. Both compute
the high product word as `sub (sub (mulMod x y (not 0)) (mul x y)) (lt mm (mul x y))`.
Generic 16573 rejects denominator <= high word; 16581 computes the power-of-two factor and
six Newton inverse refinements; 16654 combines the corrected numerator and inverse.
Do not dump the entire 16581 expression; use a named Newton-step abstraction.
The specialized routine uses division by 2^18, a high-word shift by 238, and constant
inverse 78156646155174841979727994598816262306175212592076161876661508869554232690281.
Those dependencies and the full maxMint proof are now complete; see the next section.

## Completed public maxMint

`metaMorphoV1_1MaxMintBody` is proved without placeholders and its focused build passed:
`/tmp/metamorpho-max-mint-build.log`. There are now 43 original placeholders left, including
the constructor. No differential suite or previous audit was rerun. No new assumptions or
specification changes were needed after the previously recorded cursor-model extension.

The full-precision arithmetic chain is complete in `FullMulProduct`, `FullMulTwos`,
`FullMulInverse`, `FullMulRemainder`, and `FullMulNumerator`. It proves the high product word,
lowest power-of-two factor, remainder subtraction, combined numerator, and six Newton
inverse refinements. `FullMulDivRoutines` covers generic entry 16544, and `FullMulDivWad`
covers the specialized 1e18 denominator at 16398, including all revert cases.
`FullMulDivSource` connects source function 66. `MathMulDivDownSource` and
`MathMulDivDownRoutines` cover the round-zero wrapper, source function 60 and runtime 17811.

`DecimalScale` and `DecimalScaleRoutines` prove the exact exponentiation cutoff at 77 and
the compiler routine at 14402. `ConvertSharesSource` and `ConvertSharesRoutines` prove
source function 24 and runtime entry 14489, including every checked addition and division
failure. These helpers currently cover round zero; round one remains for later callers.

`AccruedFeeSource`, `AccruedFeeRoutines`, and `AccruedFeeSimulation` complete fee charging
after the guard at 12353. `AccruedAssetsSimulation.accruedAssetsSimulation` is the complete
allocated helper from 12247 to an arbitrary valid return PC. Its success witness includes
the actual final account map, storage preservation, memory cursor and bounds, source
ExecFuncBody returning `[tuple [shares, total, lost], cursor]`, and runtime stack
`[lost, total, shares] ++ R`. It requires stack bound R.length + 35.

`AllocatedConvertSource` and `AllocatedConvertSimulation` compose that helper with
totalSupply and checked share conversion. The latter enters 2215 with
`[assets, 2234, ret] ++ R` and returns the converted word to ret, with stack bound
R.length + 38. `MaxMintEntry` and `MaxMintBodySource` provide the public boundary.
Public maxMint now reuses maxDeposit's complete simulation and scalar return encoder.

All new modules passed focused builds. Small line-wrapping edits after the public build
touch FullMulDivWad, FullMulDivSource, AccruedFeeSimulation, and AllocatedConvertSimulation;
these were included in the successful `/tmp/metamorpho-total-assets-cursor-dependencies-build.log`
rebuild, which also rechecked maxMint after the totalAssets cursor extension.
No generated block summaries were edited.

## Completed public totalAssets

The totalAssets extension has now been made and reported. `TotalAssetsAllocationSyntax`
replaces transition 0: it keeps the three entry guards, calls the allocated accrued-assets
helper with initial cursor 128, and extracts total assets from the returned nested tuple.
The helper list is still ten entries. `Spec.contract` now changes transitions 0, 19, and 59;
`Common.totalAssetsSelectorOf` unfolds the new transition. Original signatures/docstrings
are preserved. The dependency rebuild above passed.

`TotalAssetsSource` and `TotalAssetsRoutines` both pass LSP checks and focused builds.
`metaMorphoV1_1TotalAssetsBody` passed its focused build:
`/tmp/metamorpho-total-assets-build.log`. Its normal path
is 11049 -> 11055 -> 11066 -> accrued-assets entry 12247 (return PC 11075, tail `[32]`),
then the 11075 scalar encoder. There are now 42 original placeholders.
A final line-wrap in TotalAssetsSource happened after that build; include it in the next rebuild.

After totalAssets, convertToShares (60) and previewDeposit (73) share entry 1029, which
jumps to 11760; guards are at 11760 and 11766, then 11778 enters accrued-assets at 12247
with stack `[3533, 11793, 1578, 32] ++ R`. Return 3533 reads totalSupply and enters checked
add 12077, returning to 11793. That block loads calldata word 4 and enters already-proved
conversion 14489. These two public roots still need the same authorized cursor extension.
Their source can call allocatedConvertToShares with `[assets, 0, 128]` and extract result 0.

## Share views completed and asset views in progress

`convertToShares` and `previewDeposit` now have complete public proofs;
`/tmp/metamorpho-public-share-views-build.log` passed. There are 40 original placeholders.
The share-view cursor extension sets transitions 60 and 73 to `allocatedShareViewBody`,
which calls `allocatedConvertToSharesFunction` with `[assets, 0, 128]` and returns
its first component. `ShareViewEntry`, `ShareViewConversionSimulation`, and
`ShareViewSource` contain the shared entry, fee/conversion trace and source wrappers.
The simulation starts at 12247 with `[3533, 11793, ret] ++ R`, uses the already
proved accrued-assets helper, then 3533 -> checked add -> 11793 -> 14489.
It accepts arbitrary real accounts/external outcomes through `SourceState`.

Next: asset conversions. The same authorized cursor repair has now been extended
to internal function 41 `_convertToAssets` and public transitions 2/24
(`convertToAssets`, `previewRedeem`), reported immediately to the user.
`AssetViewsAllocationSyntax` appends an eleventh helper, `allocatedConvertToAssetsFunction`,
and changes those two bodies to call it with `[shares, 0, 128]`. Function27
`_convertToAssetsWithTotals` is the arithmetic helper. Shared runtime entry7734
jumps11122, guards11122/11128, then11140 ->12247 with `[3533,11155,1578,32]`.
3533 adds storage2 and fee shares;11155 loads calldata4 and jumps15343.
Latest extension awaits dependency rebuild and proofs.

## Asset views completed

`convertToAssets` and `previewRedeem` now have complete public proofs; 38 original
placeholders remain. `/tmp/metamorpho-public-asset-views-build.log` passed 3776jobs,
including shared-prefix regressions MaxMint/ConvertToShares/PreviewDeposit.
New modules: ConvertAssetsSource (function27, rounding0), ConvertAssetsRoutines
(entry15343 -> checked total+1 ->15355 -> decimal14402 ->12515 -> checkedAdd ->15337
-> MathMulDiv17811 ->11757), AllocatedAssetsSource, AssetViewEntry,
AssetViewConversionSimulation, AssetViewSource. All LSP clean and built.
`allocatedAccrualTotalsPrefixSource` in AllocatedConvertSource now factors the common
fee-accrual/cursor/totalSupply prefix for both conversion families.
The source cursor extension for asset views passed the full focused dependency build
`/tmp/metamorpho-asset-views-cursor-dependencies-build.log` (3770jobs).
Next: Math_mulDiv rounding1 for previewMint/previewWithdraw. Their public cursor
roots have not yet been extended. Their existing allocated helpers already accept
rounding parameters, but all present source/runtime conversion proofs use rounding0.

## Upward rounding and preview wrappers

`MathMulDivUp`, `MathMulDivUpSource`, `MathMulDivUpRoutines` are complete and built.
`mathMulDivUpFits := fullMulDivFits ∧ (nonzero natural remainder -> checked q+1 fits)`.
`mathMulDivUpWord` branches on remainder=0; naturalMulModSource uses unbounded
source multiplication and nonzero modulus. Runtime17811 -> fullMulDiv ->17827
->19213/19222 ->17837 ->17870 ->17881 ->17846, then17854 for exact result or
17856 checked increment ->17868; overflow9453. Stack boundR+17.
Source theorem `mathMulDivUpPrefix` differs from runtime `mathMulDivUpReachRemainder`.

ConvertShares/AssetsSource frames, OffsetValues, ArgsSource/Revert now accept optional
rounding UInt256 default0. UpSource modules reuse their argument proofs with mode1.
ConvertSharesUpRoutines starts14419 (upward checkedadd continuation14465/14478);
ConvertAssetsUpRoutines starts15275 (numerator+1,15287scale,15337reorder). All LSP clean
and built. `allocatedConvertFrame`/`allocatedAssetsFrame` have optional rounding;
PrefixSource/AccrualReverts infer an implicit rounding from the caller frame.
Allocated*Locals accepts optional mode default0; totals/argument lemmas generalized.
New AllocatedConvertUpSource/AllocatedAssetsUpSource prove only the upward tail.

Authorized cursor repair extended/reported to public previewMint53 and previewWithdraw4
via UpwardViewsAllocationSyntax; no new internal functions. Roots call existing
allocated helper with `[shares or assets, 1, 128]`, project result0. Full focused
dependency build `/tmp/metamorpho-upward-views-cursor-dependencies-build.log` passed
3786jobs, including all previous six public proofs. Width fixes and helper rebuild
`/tmp/metamorpho-upward-view-helpers-build.log` passed3736jobs afterwards.
PreviewMintEntry starts3500 ->3506 ->3518 ->12247 `[3533,3544,1578,32]`;
PreviewWithdrawEntry starts10805 ->10811 ->10823 ->12247 `[3533,10838,1578,32]`.
Shared shape of simulation preserved: R+37, source allocated frame mode1, actual
external accounts and cursor; 3544->15275 and10838->14419. Simulations and public source
wrappers LSP-clean. Public PreviewMint/PreviewWithdraw proofs written and validation
in progress at this handoff update.

## Preview build complete; withdrawal limits in progress

Both public preview proofs passed `/tmp/metamorpho-public-upward-views-build.log`
(3766 jobs). There are 36 original placeholders. `TokenBalanceCall` proves the exact
single-address balanceOf ABI request, scalar decoder, and STATICCALL at19570 with
actual source/external states. It was LSP clean before the withdrawal cursor extension.

The authorized cursor repair now also covers internal functions83 `_withdrawable`,
59 `_simulateWithdrawMorpho`, and23 `_maxWithdraw`, plus public roots63/66
maxWithdraw/maxRedeem. `WithdrawViewsAllocationSyntax` appends these three helpers
after the previous eleven, and reserves32 after balanceOf. The change was immediately
reported. Its dependency rebuild is pending. The successful runtime path19571 ->19578
->19604 ->19618 ->11329 ->19631 ->19640 ->19584 reserves32 then returns the minimum
of supplyAssets, checked(totalSupplyAssets-totalBorrowAssets), and token balance.

## Withdrawal helper and loop completed

The cursor extension passed `/tmp/metamorpho-withdraw-views-cursor-dependencies-build.log`
(3801 jobs), including all eight conversion/preview publics plus MaxMint and TotalAssets.
There are still36 original public/constructor placeholders; no new placeholders were added.
The helper list now has14 appended functions. Publics63/66 are transformed but still unproved.

New completed, LSP-clean helpers:
- `Minimum`: branchlessMinimum, minimumWord_toNat/comm, using Nat xor cancellation.
- `MinimumSource`: source/internal-call proof for originalfunction86 UtilsLib_min.
- `TokenBalanceReturn`: failure19571->2921, short/success32-byte allocation through
  19604/19618/11329/19631, then19640 reads the scalar. Generic tailR, boundsR+7/R+10/R+3.
- `TokenBalanceMemory`: returned word, cursor, protected memory; size includes max96
  because the free-pointer write can extend small memory. No assumptions added to the model.
- `TokenBalanceSource`: generic source call, decode/allocation failure, and prefix;
  requires the actual immutable MORPHO address and actual typedCallViaEVM result.
- `WithdrawableRoutines`: checkedsubtract19481->19496, call setup->19570,
  tokenBalanceReturnSize from existing callViaEVM bound, minimum return19584.
- `WithdrawableSource` and `WithdrawableSimulation`: complete allocated function83,
  runtime19481, R+13, actual external state, cursor and MemoryPrefix. All failure branches.
  `/tmp/metamorpho-withdrawable-simulation-build.log` passed.
- `WithdrawLoopSyntax`: explicit reader/arithmetic/iteration syntax for allocated function59.
  Reuses accruedAssetsCondition/Post. Originalfunction59 body kernel equality proved.
- `WithdrawLoopReaders`: parameters then supplyShares then balances, runtime16116 to16053,
  R+27 with generic tail, protects parameters through both later calls and returns loanToken load.
  `/tmp/metamorpho-withdraw-loop-readers-build.log` passed.
- `WithdrawLoopArithmeticSource/Simulation`: 3 tuple extracts, assetsDown conversion,
  allocated withdrawable call, runtime16053 ->18378 ->16063 ->19481 ->16069, R+14.
  Source continuation starts at arithmetic.drop7. Focused build passed.
- `WithdrawLoopState`: locals invariant (i/assets/cursor/no withdrawQueue local), generic
  insert/reader/converted/post/remaining preservation; zeroFloorSub then assignment and break.
- `WithdrawLoopRoutines`: queue15998->11491->16012->16116;16069 subtract/test;
  exit15984->12234. The exit does not yet execute the final checked subtraction.
- `WithdrawLoopIteration`: complete iteration, R+32, outcome break or ok, actual storage
  preservation, cursor lower/upper/size. Updated cursor result build passed.
- `WithdrawLoop`: remaining-length induction, early break, static storage preservation;
  ends12234 `[original, remaining, 12410, total, supply] ++ R`.
  `/tmp/metamorpho-withdraw-loop-build.log` passed.
- `SimulateWithdrawFunction`: full allocated function59 at15935, source init i0/for/return,
  ends12234 as above. LSP clean; focused build passed
  `/tmp/metamorpho-simulate-withdraw-function-build.log`.
  Three line-width fixes after this build affect WithdrawLoopArithmeticSimulation,
  WithdrawLoopState, and SimulateWithdrawFunction; include them in the next checkpoint build.

Important runtime naming correction: loop15976 stack is
`[MORPHO, i, original, remaining, total, supply, len] ++ R`.
The original amount is x2 and current remainder is x3. The early-break stack at16091
swaps the first two entries;15984 ignores those heads. No source-model mismatch.

Next: originalfunction23 `_maxWithdraw`, allocated helper. Source indices after cursor expansion:
0..3 initialize assets/newTotalSupply/newTotalAssets/feeShares;
4..6 allocated accrued call;7 assign feeShares;8 assign newTotalAssets;9 totalSupply_body;
10 checked assign newTotalSupply;11 balanceOf_body(owner);12 asset conversion mode0;
13 assign assets;14..16 allocated simulate-withdraw call;17 checked assets-minus-remainder;
18 return nested triple plus cursor. Need kernel syntax lemmas for these indices.
No internal balanceOf_body proof exists yet; originalfunction58, source can use
MappingStorage.evalStorage_balanceOf with canonical owner. Runtime15882 ->12247
returns15894 `[lost,total,feeShares,owner,15935] ++ R`, then checkedAdd to15909.
15909 hashes owner (slot0), reads balance and enters15343 conversion, then15935 loop.
Final checked subtraction12234 returns12410, which reorders `[assets,total,supply,ret] ++ R`
to `[total,supply,assets] ++ R` at ret. RootmaxWithdraw return1970 extracts the scalar;
rootmaxRedeem return1572 enters share conversion14489.

## Public withdrawal limits completed

`MaxWithdraw` and `MaxRedeem` are now proved, reducing the original placeholders to34.
Both are LSP-clean. Their joint focused build passed in
`/tmp/metamorpho-public-withdraw-views-build.log`.
The separate MaxWithdraw build passed3773jobs. All helper builds below passed.

New modules: BalanceInternalSource (originalfunction58 balanceOf_body), MaxWithdrawBalance
(slot0 owner hash and memory preservation), MaxWithdrawSource (zero locals and accrued call),
MaxWithdrawConversionSource/State/ConversionSimulation (checked supply addition, balance,
assets conversion), MaxWithdrawTailSource (simulation call and checked final subtraction),
MaxWithdrawFunction (whole allocatedfunction23), WithdrawViewEntry (shared Bool-selected
maxWithdraw/maxRedeem guards and address decode), MaxWithdrawBodySource,
MaxRedeemBodySource, MaxRedeemReturn. No spec/model changes in this context.

`maxWithdrawFunctionSimulation` starts15882 `[ownerWord,ret]++R`, boundR+38, and returns
actual source/external state, storage preservation, cursor≥96 and memory≥96,
source tuple[assets,supply,total]+cursor, and runtime ret `[total,supply,assets]++R.
It includes every accrual, checked-add, conversion, liquidity-loop, and subtraction failure.
`maxWithdrawConversionSimulation` starts15894, boundR+20, and ends15935; memory becomes
twoWordHashMem ownerWord0mem, whose size and cursor are preserved for96≤mem.size.

Generalized session-created `withdrawLoopSimulation` and `simulateWithdrawFunctionSimulation`
to require only96≤mem.size (plus cursor≥96/free), removing cursor<2^64 and cursor≤mem.size
inputs and outputs. This is necessary for empty queues with initial cursor128/memory96.
Actual iterations still provide stronger bounds from successful allocations. No model change.
The prior AccruedAssetsSimulation API is unchanged (a temporary strengthening was undone).

`WithdrawViewEntry` Boolean false selects1940/ret1970/stack[1970,32]; true selects1534/
ret1572/stack[1572,1578,32]. Shared11163->1567->15882, boundR+8. Canonical address conversion
uses `keyValueToWord_address` before `keyValueToWord_address_of_canonical`; they are not
definitionally the same as UInt256.ofNat(address.toNat), and attempting exact caused slow whnf.
maxWithdraw1970 encodes the third stack word. MaxRedeem1572 reorders then14489 share conversion,
1578 scalar encode. Source three tuple extracts need `dsimp only[maxRedeemPublicTail,List.append]`
and separate `apply consNormal` / `exact h` to avoid expensive elaboration at the third let.

Other completed builds: max-withdraw-balance, max-withdraw-source (3740jobs),
max-withdraw-conversion-source, max-withdraw-tail-source, max-withdraw-state,
max-withdraw-conversion-simulation, max-withdraw-function, withdraw-public-helpers,
max-redeem-source, max-redeem-return, all logs `/tmp/metamorpho-<name>-build.log`.
Line-width check and git diff --check passed; one101-column MaxWithdrawBodySource line was
wrapped before the current joint public build. Earlier three loop width fixes are built.

## Public approval completed

`Approve` is proved, reducing original placeholders to 33. LSP clean and focused build passed
(`/tmp/metamorpho-public-approve-build.log`). No model changes or assumptions added.
New modules: ApprovalSource (original functions 72 and 36), ApprovalCalls, ApproveBodySource,
ApprovalStatic, ApprovalRoutines, ApproveEntry. All helper builds passed. One formatting-only
line wrap in ApprovalSource followed the public build; include it in the next dependency build.

ApprovalSource covers the bool event overload, both zero-address guards, nested allowance
storage writes, and static failure. ApprovalCalls proves both call wrappers and `_msgSender`.
Runtime 16692 checks owner; 16709 checks spender; 16725 writes nested mapping slot 1, emits,
and returns. Static proof stops at SSTORE 16782. Public entry 10846 checks nonpayability/length,
11163 decodes the address, 10874 loads value/caller; 4161 encodes true.
`approvalStoreReturn` has arbitrary memory/stack tail; no allocation invariants needed.
`approvalScratchMem` is two nested twoWordHashMem writes; `approvalReturnMem` adds event data.
Canonical address masks require an explicitly typed UInt256 mask equality, not inferred
`EVM.word` notation. Hash normalization similarly uses typed keccakWord equalities.

Next active work: Transfer, first the shared `_update` source/runtime helper (function 73).
Source `_update`: from-zero checked supply add; otherwise balance read, sufficient-balance
guard, wrapping debit. Then to-zero wrapping supply debit, otherwise wrapping balance credit
read from the already updated storage. Preserve this order without collision assumptions.

## Public transfer completed

`Transfer` is proved, leaving 32 original placeholders. Focused builds passed both before and
after formatting (`/tmp/metamorpho-public-transfer-build.log`,
`/tmp/metamorpho-transfer-format-build.log`, 3539 jobs). No model changes or assumptions.
New helper modules: BalanceMutation, BalanceUpdateSource, TransferInternalSource, TransferGuards,
TransferBodySource, TransferRoutines, TransferStatic, TransferEntry. All are built/LSP clean.
BalanceUpdateSource proves the nonzero-address path of function 73 `_update`; mint and burn
branches are still to be proved when needed. TransferInternalSource proves function 42
`_transfer`, including zero-address guards, insufficient balance, and static violation.
BalanceMutation keeps the recipient balance read after the sender write; no slot-noncollision
or sender/recipient inequality assumptions. Wrapping casts use signedAddWrap/signedSubWrap.

Runtime transfer: 12728 sender guard -> 12745 recipient guard -> 12761 balance check -> 12780
stores/emits/returns. Zero-address reverts 12898/12879; insufficient balance reverts 12854.
First SSTORE 12829 is separately proved for static execution. Store bound is R+10.
Public entry 4123 -> 4129 -> 4141 -> 11163 -> 4151 -> 12728, return 4161 reused from ApproveEntry.

Current work: TransferFrom. AllowanceInternalSource (function 74), SpendAllowanceSource
(function 43), and SpendAllowanceCalls are written, LSP clean; first two focused builds passed,
Calls build running in `/tmp/metamorpho-spend-allowance-calls-build.log`.
Source allowance helpers distinguish unlimited (`UInt256.lnot 0`) from finite. Finite path
checks sufficiency before owner/spender address guards and then writes without an event.
SpendAllowanceCalls exposes Allowed, State, call success/revert/static and environment equality.
Runtime allowance work still pending: 12530 hashes/reads, unlimited -> 12579 return, finite ->
12585 balance guard -> 12593 owner guard -> 12599 spender guard -> 12614 SSTORE -> 12579 return.
12614 stores allowed-value and pushes four zeros ahead of the return PC; bound R+7.
Public TransferFrom: 10441/10447 nonpay/96-byte check; 10459 -> 11163 -> 10469 -> 11185 ->10477.
10477 calls 12530 with [from,caller,value,10492,from,to,value,4161]; 10492 ->12728 Transfer routine.

