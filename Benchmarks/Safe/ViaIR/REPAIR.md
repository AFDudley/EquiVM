# Safe via-IR repair status

The port is incomplete: 32 of 33 runtime obligations now build, including
`execTransaction`. `setup` and the final whole-contract checks remain. The setup
investigation has found an additional allocation boundary mismatch; its checked
evidence and proposed local correction are described at the end of this report.

Artifact regeneration and the executable semantic gates passed;
constructor, shared dispatcher, and generated block summaries build. The huge-calldata
counterexample is addressed by a user-authorized decoder correction local to this benchmark.
The remaining runtime proofs and whole-contract axiom audit have not been completed. A second,
formally checked counterexample exposed an absent-account mismatch. The user authorized an
account-existence premise on affected runtime claims; that restriction is now implemented in
the add-owner theorem and the runtime and whole-contract statements, using the existing WF
refinement relations. Shared storage semantics and the specification are unchanged for it. A third certified
counterexample exposed the IR storage reader's final allocation-pointer check. The user
authorized tightening only the existing `getStorageAt` allocation guard. That change is
applied, and the complete `getStorageAt` refinement theorem now builds. Continuing the
port exposed the analogous owner-array allocation mismatch below. Its separate local guard
correction is now approved and applied; the full `getOwners` refinement theorem builds. The separately approved paginated-module guard correction is applied;
its complete entrypoint refinement theorem now builds.

Twenty-five runtime obligations now build: receive, fallback, `nonce`, `getThreshold`, `signedMessages`,
`approvedHashes`, `isOwner`, `isModuleEnabled`, `domainSeparator`, `VERSION`, `changeThreshold`,
`setFallbackHandler`, `approveHash`, `enableModule`, `disableModule`, `swapOwner`,
`addOwnerWithThreshold`, `removeOwner`, `getStorageAt`, `getOwners`, `getModulesPaginated`,
`setGuard`, `setModuleGuard`, `simulateAndRevert`, and `getTransactionHash`. The zero-argument
proofs include the new signed length failure; the mapping getters include short, huge, and
noncanonical calldata where applicable. Fallback covers handler absence, call success and
failure, static callers, call-depth failure, and oversized calldata exhausting gas.

Their bytecode traces were repaired in place. Decoder and return-routine interfaces now use the
IR entry PCs and stack layouts; removed legacy tuple-decoder paths were replaced by the inlined
checks at their callers. The bytes32 decoding lemma keeps its statement and proof in the calldata
layer. The existing selector-miss fold also proves arrival at the final selector arm, whose
comparison consumes the selector. The module-membership trace uses the new branch order and
preserves its memory guarantees. Source evaluation lemmas retain their statements except for the approved allocation bound;
the approved public-statement exception is described below. The authorization and owner-validation traces now follow the IR's subtraction
tests and changed stack order, including the delegated-account branch. Owner insertion/removal
guards retain their memory-preservation conclusions. Pair/triple address decoding follows the
inlined external entry paths and the three shared single-address routines. State-changing
traces cover their new storage-write order, static violations, and inlined threshold/event
returns. The scratch-memory preservation lemma was moved unchanged to the existing byte-copy
layer to avoid importing unrelated, still-unported module execution traces.

Solc `0.8.35+commit.47b9dedd`, with only `--via-ir` added, produces an 11,003-byte runtime and
11,034-byte creation program. The constructor prelude shrinks from 33 to 31 bytes and copies
the runtime into memory at 128 instead of 0. The binary dispatcher becomes a linear selector
chain starting at PC 168, retaining an additional zero word on the stack. Receive and fallback
precede that chain; external bodies are inlined and internal routines are reorganized. There
are 1,871 runtime summary theorems in 49 shards, 6,974 summarized instructions, and 26 explicit
boundaries, compared with 1,937, 51, 7,844, and 20 in the legacy baseline.

The regression audit reports 408 cases and `failures 0`, with unchanged outcome counts. Its
four gas-observation PCs were updated from the compiler source map; no expected outcomes
changed. The randomized summary is:

```text
Safe_ViaIR: 1775 cases: 1762 agree (580 successful), 0 disagree, 0 stuck, 13 EVM out of gas, 0 spec out of fuel
```

The current randomized run uses the rebuilt executable from the EVM dependency directory
with an isolated Python environment containing `coincurve`, `pycryptodome`, and
`typing-extensions`. It completes without precompile errors. An earlier root invocation
reported missing Python precompile support; the corrected invocation avoids that issue.

Statement changes so far: `safeCreationRuntime` uses the new code offset, length, and memory
offset; `safeReachShort` reaches PC 14 instead of 475; `safeReachSelectorGroup` and `safeReachEntry`
retain the extra zero stack word. `safeSelectorStart` is now the constant PC 168. These describe
changed code. The constructor traces and selector-group proof were reproved in place, using the
new summaries and existing opcode lemmas. `safeAddownerwiththresholdRefines` now requires
`σ.get? I.codeOwner ≠ none`, as explicitly authorized. `safeCorrect` and `safeContractCorrect`
use `runtimeRefinementWithWF` and `contractRefinementWF` with that predicate and `noGasBound`.
The constructor and the other entrypoint declarations keep their original statements;
`config` incorporates the local decoder correction described below. The constructor axiom check reports only
`propext`, `Classical.choice`, `Quot.sound`, and native-decide certificates. No proof holes or
custom axioms were added.

The transaction-hash entrypoint also builds with its original public statement. Its calldata
bytes decoder and inlined tuple checks follow the IR branches, including rejection of
noncanonical addresses, invalid operations, and out-of-bounds dynamic data. The hashing trace
proves the fused transaction-struct stores, domain separation, final preimage, and free-pointer
preservation. Internal trace statements reflect the new PCs and stack order; the hash and
calldata specifications are unchanged. The compiled refinement theorem uses the standard
three axioms and 471 native certificates, with no proof holes or custom axioms.

Generated `safeRuntime_block_4770` initially exceeded Lean's default recursion limit while
normalizing gas counters. With explicit user approval for the two generator-script edits,
the block renderer now accepts an optional recursion limit and the Safe audit enables 10,000
for `--via-ir` runtime output. Default generation was checked byte-for-byte unchanged; the IR
change only adds the option and updates index line numbers. All 49 regenerated runtime shards
and the aggregate `Blocks` target now build successfully. `Main`, the source tree, source
manifest, and shared libraries remain untouched.

A former blocker was the signed length check in the zero-argument `nonce()` body. At PCs
4025–4035, the IR code tests `SLT(CALLDATASIZE - 4, 0)` and jumps to the empty revert at
PC 589 when the result is nonzero. Take the nonce selector `0xaffed0e0`, append `2^255`
zero bytes, set call value to zero, and give the runtime 1,000 gas. Its calldata length is
`2^255 + 4 < 2^256`, so it meets the existing theorem's bound. The shared `modern` ABI decoder
accepts it and the source body returns normally. The actual bytecode instead reverts after
111 instructions, leaving 540 gas. Gas exhaustion therefore cannot cover the discrepancy.

The counterexample constructs the byte array symbolically; it does not allocate or evaluate
an enormous buffer. Lean's logical `ByteArray` has no machine-size bound. The execution
certificate checks each opcode of the actual runtime, including its selector dispatcher.

The authorized specification change adds `safeDecodeCalldata` and installs it only in this
benchmark's `config.externalABI.decodeCalldata?`. For empty parameter lists it rejects
`calldata.size - 4 >= 2^255`, matching the generated signed guard under the existing
`calldata.size < 2^256` premise. All other inputs use the existing `modern` decoder. No shared
decoding mode or theorem input bound changed. That decoder correction did not change the contract bodies or syntax spec; the later
allocation correction below changes one guard in both specifications.

`safeDecodeCalldata_eq_modern_of_small` proves equality with the original decoder below the
first rejected length; `safeDecodeCalldata_cons` proves equality for every nonempty parameter
list. `safeIRHugeNonceCalldata_decodingFailed` proves the formerly accepted input is rejected.
The original 111-instruction execution certificate is retained, and `safeIRHugeNonceRefines`
now matches that exact revert using `runtimeRefinementFor.decodingFailed`. It replaces the
refutations of the superseded configuration. Rebuild this regression certificate with
`lake build Benchmarks.Safe.ViaIR.IRLengthCheckTrace`.

Validation after the local correction: the regression certificate, constructor, artifact checks,
and 408-case audit build successfully; the randomized test retains the summary above. The
manifest's specification hash was regenerated, and the no-write artifact audit passes. The
decoder equivalence lemmas use only standard Lean axioms. The exact refinement regression uses
`propext`, `Classical.choice`, `Quot.sound`, and 115 native-decide certificates, with no other
axioms or proof holes.

This formal input is outside physically realizable calldata, which explains why the passing
finite audits do not detect it. The local specification correction resolves this particular
discrepancy; the remaining runtime proof repair is still required for whole-contract correctness.

The absent-account counterexample is independent of ABI decoding. With an empty account map, set both caller and
code owner to `0x1000`, provide the actual runtime as `I.code`, and call
`addOwnerWithThreshold(0x2000, 1)` with zero value, write permission, and 100,000 gas. The input
is 68 bytes and satisfies every original public premise. The actual `Ξ` execution succeeds,
returns empty bytes, and leaves 28,205 gas. The source transition reverts: both models make
storage writes to an absent account no-ops, so the source reads owner count zero after assigning
one. The IR retains the computed one on its stack at PC 6831 and compares the new threshold
against it at PC 6891, without reloading slot 3.

`safeIRAbsentOwnerPremises` and `safeIRAbsentOwnerDecoding` check the input and successful
decoding. `safeIRAbsentOwnerExecution` certifies the actual EVM success and gas remainder;
`safeIRAbsentOwnerSourceReverts` constructs the source derivation. The independent inversion
proof `safeIRAbsentOwnerSourceCannotReturn` excludes every successful source derivation,
including the relation's alternative control-flow constructors. Consequently,
`safeIRAbsentOwnerNotRefines` proves the negation of `runtimeRefinementFor` for this input.
Build the witness with `lake build Benchmarks.Safe.ViaIR.IRAbsentAccount`.
The witness builds, and its axiom audit contains the standard three axioms and eight
native-decision certificates. Before the allocation correction, the combined build of all eighteen repaired entrypoints
and both negative regression witnesses passed (3,581 build jobs). The newly repaired public proofs pass individual
axiom scans with only the permitted axioms and native certificates. No proof holes or custom
axioms were added.

This is a gap between the theorem's unrestricted input domain and the model's storage
semantics. The witness supplies executable code separately from the absent account; it is not
evidence of a compiler error on ordinary deployed-account execution. The user approved
requiring an existing executing account in affected runtime claims. The add-owner proof now
preserves account existence across its link updates and proves that the incremented count is
retained in storage. Remove-owner needs no added premise: its nonzero-count guard already
implies account existence. Its proof follows the IR's fused decrement/store, two owner-link
writes, and inlined threshold check. The counterexample is retained as evidence for the domain
restriction; it does not refute the restricted claim. The storage-read allocation discrepancy
below was found while continuing the remaining runtime obligations.

The allocation counterexample uses an existing account and only 68 bytes of calldata:
`getStorageAt(0, 2^59 - 1)`, zero call value, write permission, and 100,000 gas. The requested
byte length is `2^64 - 32`, so the original source guard `maxMemoryLength = 2^64 - 1` accepted it.
The IR computes an allocation size of `2^64`, then adds its initial free pointer 128. Its
`finalize_allocation` check at PC 7128 branches to the allocation panic at PC 7161. The actual
EVM execution reverts with panic `0x41`, leaving 99,481 gas; it never attempts the enormous
memory allocation or storage-read loop.

`safeIRStorageAllocationPremises` checks every original premise and the newly authorized
account-existence condition. `safeIRStorageAllocationDecoding` proves that the local decoder
accepts the two words. `safeIRStorageAllocationExecution` certifies the actual revert and gas
remainder. Before the correction, structural inversion of every source-loop result proved
that this accepted call could not revert, establishing a certified negative runtime claim.
That evidence is retained in commit `ef850b76`.

The user approved replacing the bound in `getstorageatTransition`'s existing allocation guard
by `2^64 - 161`, mirrored in the syntax specification. This requires
`requestedBytes + 160 <= 2^64 - 1`, accounting for the initial 128-byte pointer and 32-byte
header. The shifted byte length is a multiple of 32, so its largest admitted value is
`2^64 - 192`. `safeIRStorageAllocationCorrectedBound` verifies the arithmetic equivalence,
and `safeIRStorageAllocationRejectedByCorrectedBound` verifies rejection of the witness.
The shared `maxMemoryLength` and ABI decoding modes are unchanged.

`safeIRStorageAllocationSourceReverts` now constructs the matching source revert, and
`safeIRStorageAllocationRefines` proves refinement for the exact formerly failing input.
The original bytecode execution certificate and input facts are retained; superseded
refutations are replaced by this positive regression. Its axiom scan contains the standard
three axioms and eight native certificates, with no proof holes or other axioms.

The complete `safeGetstorageatRefines` theorem now builds with its original statement. Its
trace follows the two IR allocation checks, reversed header/free-pointer write order, new
storage-loop stack, and shared byte-copy return routine. The loop invariant and source
induction are retained. The gas argument covers shifted lengths that wrap and would require
at least `2^251` iterations; an explicit opcode derivation preserves its gas lower bound.
The theorem's axiom scan reports 348 axioms: only the standard three and native certificates.
The source guard lemmas use the approved bound. Trace helper statements change only to match
the new PCs, stacks, memory order, and copy-loop header-relative addresses.

After this correction, the 408-case audit reports zero failures and the randomized test
reports the summary above. The manifest hashes were regenerated and the no-write artifact
audit reproduces the unchanged bytecode and block summaries. The storage-reader theorem and
positive regression build together (3,513 build jobs). A combined build of all nineteen
repaired entrypoints and the three regression witnesses also passes (3,593 build jobs).
Whole-contract correctness still requires completing the remaining runtime obligations.

The fourth certified discrepancy was `getOwners` with an existing executing account,
four-byte calldata `0xa0e67e2b`, zero call value, and 100,000 gas. Slot 3 contains
`2^59 - 1`, and the owner sentinel mapping points to itself. The previous specification
accepted the count (`<= 2^64 - 1`), created the zero-filled array, skipped the traversal,
and returned it. The IR computes `32 * count + 32 = 2^64`, then its final pointer check
rejects the allocation. Actual EVM execution returns panic `0x41` and leaves 97,240 gas.
The negative refinement certificate is preserved in commit `86a0e8e4`.

The user separately approved changing only the existing `getOwners` count guard to
`ownerCount <= 2^59 - 6`, mirrored in the syntax specification. That change is applied.
`safeIROwnerAllocationCorrectedBound` proves this is equivalent to
`32 * ownerCount + 160 <= 2^64 - 1`; `safeIROwnerAllocationRejectedByCorrectedBound`
checks the witness. Shared memory bounds, decoding modes, and other transitions are
unchanged by this correction. The former negative witness has been converted into the
positive regression `safeIROwnerAllocationRefines`, with the actual bytecode execution
certificate retained. The complete `getOwners` refinement proof now follows both IR
allocation checks, the free-pointer/header write order, address-array traversal and
bounds panic, and the new ABI encoder. Its public statement is unchanged. Source
count premises use the approved local bound; trace interfaces reflect the new PCs
and stack layouts. The array-copy invariant and return encoding are preserved.

All twenty repaired entrypoints, the allocation/account regression modules, and the
huge-owner memory audit build together (3,603 jobs). The `getOwners` theorem uses only
the standard three axioms and 429 native certificates. The positive allocation
regression uses the standard three and five native certificates; neither scan found
proof holes or additional axioms.

After this guard change, artifact reproduction passes, the executable audit reports
408 cases and zero failures, and the randomized differential run reports:

```text
Safe_ViaIR: 1775 cases: 1758 agree (577 successful), 0 disagree, 0 stuck, 17 EVM out of gas, 0 spec out of fuel
```

The fifth certified discrepancy was `getModulesPaginated(1, 2^59 - 1)` with an existing
executing account, 68-byte canonical calldata, zero value, 100,000 gas, and
`modules[1] = 1`. The previous specification accepted `pageSize <= 2^64 - 1`,
counted zero modules, and returned an empty array with next pointer 1. The IR calls
the same array allocator before traversing the list: `32 * pageSize + 32 = 2^64`,
and its final-pointer check reverts with panic `0x41`, leaving 99,080 gas.
This input satisfies the approved account-existence restriction and uses ordinary
ABI decoding. The negative certificate is preserved in commit `4495cf25`.

The user separately approved replacing only `getmodulespaginatedTransition`'s existing
page-size guard with `pageSize <= 2^59 - 6`, mirrored in the syntax specification.
That change is now applied. `safeIRModuleAllocationCorrectedBound` proves equivalence
to the allocator's `32 * pageSize + 160 <= 2^64 - 1` condition. The former counterexample
now checks as the positive regression `safeIRModuleAllocationRefines`, retaining the
actual EVM execution certificate. The complete entrypoint proof now builds with its original
statement. It follows the inlined address and length decoding, sentinel/membership checks,
two allocation checks, module traversal, last-element selection, and shared array encoder.
The linked-page source induction and memory invariant are retained. Source bound premises
use the approved page-size limit; trace helper interfaces match the IR PCs and stack layouts.
The last-element trace explicitly uses the existing canonical-address invariant because
this IR path masks the loaded address before return.

The entrypoint axiom scan reports the standard three axioms and 816 native certificates;
the positive regression uses the standard three and eight native certificates. Neither
scan found proof holes or additional axioms. The no-write artifact audit reproduces the
bytecode and block summaries. All twenty-one repaired entrypoints and the regression
modules build together (3,620 jobs). Whole-contract correctness still requires the
remaining twelve runtime obligations.

After this correction, artifact reproduction passes and the executable audit reports
408 cases with zero failures. The randomized differential run reports:

```text
Safe_ViaIR: 1775 cases: 1762 agree (580 successful), 0 disagree, 0 stuck, 13 EVM out of gas, 0 spec out of fuel
```

Both guard setters now build with unchanged public statements. Their traces use the new
inlined external entry paths, shared authorization routine, fixed 32-byte static-call
output buffer, checked allocation, canonical bool decoder, storage write, and event/return.
The return-memory invariant now uses `min 32 out.size`, matching the IR's bounded buffer.
Source call and state-update proofs are retained. False, short, and noncanonical return
values, failed calls, unauthorized callers, and static writes are covered. Direct axiom
audits report 426 permitted axioms for `setGuard` and 433 for `setModuleGuard`.

`simulateAndRevert` also builds with its original public statement. The dynamic-memory
bytes decoder and address/bytes entry trace were ported in place, preserving the proof
that decoding either reverts or reaches the delegate call. Every delegate-call outcome
reaches the final revert; the source proof is unchanged. Its axiom audit reports only
the standard three axioms and 374 native certificates. The two guard setters and simulation
build together (3,529 jobs), with no proof holes or custom axioms.
All twenty-four repaired entrypoints and the regression modules build together
(3,647 jobs). Nine runtime obligations remain before the whole-contract check.

The signature-decoder and loop-foundation checkpoint builds successfully (3,594 jobs).
Both counted and uncounted overloads, with explicit or implicit executor addresses, now
follow the inlined IR entry decoders. The memory-bytes decoder and encoder retain their
source-level bounds and memory contents; their PCs, stack interfaces, and stack-height
premises match the new routines. The return-word decoder now describes its inlined module
return path. Unused transitive imports of legacy module traces were removed.

The signature loop's initial bounds check, signature splitting, owner ordering and membership,
approved-hash branch, and full P-256 branch are repaired. The IR drops unused signature words
between iterations, specializes multiplication by 65, and inlines P-256 verification. Internal
trace interfaces and the branch-result invariant reflect those changes. The removed generic
checked-multiplication subroutine is replaced by proofs of the actual generic and specialized
IR multiplication paths. No public entrypoint statement or specification changed in this
checkpoint. Axiom scans found 508 permitted axioms for legacy decoder evidence and 379 for the
P-256 branch, with no proof holes or custom axioms. The remaining signature branches and the
whole-contract proof are still in progress.

The ECDSA and `eth_sign` branch checkpoint builds successfully (3,545 jobs). The IR uses
the free-memory pointer directly for the ECRECOVER input and a zeroed scratch word for
its output. The memory and call traces now describe that layout, including call failure
and empty output. The `eth_sign` prefix allocation rounds its 92 bytes up to 96 and checks
the resulting pointer. Its allocation-failure path is covered under the existing source
call semantics, which abstracts call gas: a zero-gas ECRECOVER call fails, and the source
requirement then reverts. This fact is proved from the precompile semantics. No specification
or public entrypoint statement changed. Axiom scans report 80 permitted axioms for ECDSA
and 187 for `eth_sign`, with no proof holes or custom axioms. Contract signatures and the
remaining entrypoint integration are still in progress.

All four public signature-check entrypoints now build with their original statements
(3,642 jobs). The contract-signature branch follows the IR's specialized bounds checks,
inlined call encoding, checked allocation, static call, return-buffer allocation, and
magic-value validation. The obsolete second forward copy is removed from its memory
model. Allocation failures are covered under the existing source call semantics: a
zero-gas contract-signature call cannot return an accepted 32-byte magic value. That
rejection lemma is proved from ordinary EVM and precompile semantics and uses only
the standard three axioms. No specification change was needed.

The signature iteration and loop retain their source invariant and induction. Internal
trace interfaces now describe the IR's smaller stack, branch targets, and return paths.
All signature modes, count and threshold checks, authorization, and decoding-failure
paths are joined to the four public proofs. Their axiom audits report 2,065 and 1,960
permitted axioms for the two `checkNSignatures` overloads, and 2,126 and 2,021 for the two
`checkSignatures` overloads, with no proof holes or custom axioms. Twenty-nine of the
thirty-three runtime obligations are complete. Module execution, transaction execution,
and setup remain before the whole-contract validation.

Both module execution entrypoints now build with their original public statements
(3,578 jobs). Their proofs follow the IR's shared argument decoder, module authorization,
optional pre-execution guard, specialized CALL/DELEGATECALL routine, post-execution guard,
and event/return paths. The returndata variant preserves and encodes the full call output.
The pre-guard return buffer uses `min 32 out.size`; the post-guard's zero-length allocation
still validates its free-memory pointer. Internal trace interfaces and memory invariants
were updated for those instructions and their smaller stacks.

An allocator rejection after a nonzero module guard is covered by a reverting source
pre-guard call under the existing gas abstraction. A zero-gas call with the encoded
`checkModuleTransaction` input produces no return bytes, so it cannot satisfy that call's
bytes32 result decoder. The empty-output fact is proved from EVM and precompile semantics
and introduces no axioms. No specification or public statement changed. The two entrypoint
axiom scans report 1,024 and 1,063 permitted axioms, with no proof holes or custom axioms.
Thirty-one of the thirty-three runtime obligations are complete; transaction execution
and setup remain before whole-contract validation.

The transaction decoding and pre-guard prefix now build together with all four signature
entrypoints (3,664 jobs). Decoding follows the inlined entry path and specialized address
readers, retaining the existing malformed-input and size-bound cases. The nonce increment,
static-write rejection, transaction hash, and signature call use the new stack layouts.
The prefix and decoder evidence scans report 1,862 and 530 permitted axioms, respectively.

The signature memory invariant now also records that a free pointer below `2^64` remains
below that bound. Branches either retain the pointer or pass an existing checked allocator;
this stronger fact is propagated through the signature loop. It is needed by the IR's
zero-length allocation after the transaction guard call. The source specification and
public entrypoint statements are unchanged. Transaction execution and setup are still
being integrated.

The transaction guard, gas checks, calldata allocation, CALL/DELEGATECALL, gas-used
accounting, and success check now build together (3,643 jobs). Their internal interfaces
follow the IR's smaller stacks, calldata reloads, checked memory allocation, and new
branch targets. Guard-call encoding preserves both dynamic byte arrays and the caller
address, and its successful zero-length allocation retains the free pointer below
`2^64`. Both execution modes include their static-call rejection paths.

Calldata allocation can fail at the IR's pointer bound. At the enclosing transaction gas
check, that rejection is covered by the existing source gas abstraction: choosing zero
gas either overflows the required-gas arithmetic or fails its positive gas requirement.
The rejection lemma uses only the standard three axioms; no specification change was
needed. The execution, gas-used, and success-check axiom scans report 280, 33, and 70
permitted axioms, with no proof holes or custom axioms. Refunds, transaction completion,
setup, and the whole-contract checks remain in progress.

The public `execTransaction` refinement now builds with its original statement. Its
inlined refund path covers receiver selection, checked arithmetic, native and token
calls, token return-value validation, and return-buffer allocation. Token calldata
reserves 128 bytes for its 100-byte buffer. Allocation failures propagate to the
transaction's existing gas-check rejection proof. The event, post-execution guard,
zero-length guard allocation, and boolean return follow their new IR paths. No
specification change was needed.

The return-buffer allocator proof is shared with contract-signature checking; the
signature entrypoint regression audit also passes. Transaction completion and signature
audits build together (3,730 jobs). The public transaction theorem uses 3,565 permitted
axioms; the token-transfer and payment traces use 162 and 624. No proof holes or custom
axioms were found. Thirty-two of the thirty-three runtime obligations are complete.
Setup and the final whole-contract checks remain.

The setup investigation confirms an additional data-allocation mismatch. A symbolic,
well-formed call has one owner (`0x2000`), threshold one, zero target, fallback and
payment, and `data.length = 2^64 - 255`. Its calldata size is `2^64 + 101`.
The benchmark's existing decoder accepts it. The input owner array leaves the free
pointer at 192; copying the data reserves a 32-byte header and rounds its payload
up to `2^64 - 224`, making the final pointer exactly `2^64`.

The checked allocator execution starts at the actual data-copy entry PC 7208 with
that stack and pointer. It reaches panic `0x41` with more than 99,000 of its 100,000
gas remaining, before attempting the large copy. This is an allocator-segment
certificate, not a new complete entrypoint execution certificate or a formal
negation of the public setup theorem. Separately, Lean verifies successful decoding,
the exact symbolic payload and scalar arguments, and that the corresponding
zero-target `setupModules` source body returns and cannot revert. The new evidence
module builds; its axiom scans contain only the permitted axioms and native
certificates.

The approved local correction is one requirement immediately after `SafeSetup`:
`32 * _owners.length + data.length <= 2^64 - 224`, mirrored in the syntax spec.
Lean proves this is exactly equivalent to the data allocator's final-pointer
condition `160 + 32 * owners.length + 32 + paddedSize(data.length) < 2^64`.
It also implies the earlier input-owner allocation fits. It rejects the example
while accepting the immediately preceding payload length with one owner. It
preserves the event's static-mode behavior and leaves shared decoding modes
unchanged. Both specification representations now include the approved guard,
and Lean proves that the source rejects the symbolic boundary input. Artifact
regeneration passes, the audit reports 408 cases and zero failures, and the
randomized run reports `1775 cases: 1759 agree (579 successful), 0 disagree,
0 stuck, 16 EVM out of gas, 0 spec out of fuel`.

Setup's inlined decoder is ported through PC 3163, including all malformed-head,
offset, length, and address-canonicality rejection paths. Its two bytecode proofs
use 218 and 441 permitted axioms, respectively; both pure decoder proofs use the
standard three. The decoder audit and guard regression build together (3,589
jobs). The remaining setup body and final whole-contract checks are in progress.
