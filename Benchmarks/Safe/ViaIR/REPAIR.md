# Safe via-IR repair status

The port is incomplete. Artifact regeneration and the executable semantic gates passed;
constructor, shared dispatcher, and generated block summaries build. The huge-calldata
counterexample is addressed by a user-authorized decoder correction local to this benchmark.
The remaining runtime proofs and whole-contract axiom audit have not been completed. A second,
formally checked counterexample exposed an absent-account mismatch. The user authorized an
account-existence premise on affected runtime claims; that restriction is now implemented in
the add-owner theorem and the runtime and whole-contract statements, using the existing WF
refinement relations. Shared storage semantics and the specification are unchanged for it. A third certified
counterexample exposed the IR storage reader's final allocation-pointer check. The user
authorized tightening only the existing `getStorageAt` allocation guard. That change is
applied, and the complete `getStorageAt` refinement theorem now builds.

Nineteen runtime obligations now build: receive, fallback, `nonce`, `getThreshold`, `signedMessages`,
`approvedHashes`, `isOwner`, `isModuleEnabled`, `domainSeparator`, `VERSION`, `changeThreshold`,
`setFallbackHandler`, `approveHash`, `enableModule`, `disableModule`, `swapOwner`,
`addOwnerWithThreshold`, `removeOwner`, and `getStorageAt`. The zero-argument
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
