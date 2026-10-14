# Safe Benchmark

Source: [`contracts/Safe.sol`](contracts/Safe.sol) from `safe-fndn/safe-smart-account` commit `cdb2eb578dbdba4c3f10a47f9a2dd9580773e63a`.

Compiled with Solidity 0.8.35 and optimizer enabled, from the repository root:

```bash
solc --optimize --optimize-runs 200 --evm-version shanghai --metadata-hash none --bin --bin-runtime --abi --storage-layout \
  --base-path . --overwrite -o /tmp/safe-v0-build Benchmarks/Safe/V0_cdb2eb5/contracts/Safe.sol
```

Pinned compiler: `0.8.35+commit.47b9dedd.Linux.g++`, sha256
`fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4`.

The EVM target is pinned to Shanghai to reproduce the original artifacts. The current local
EVM semantics also implement `MCOPY`; changing the compiler target would still change the
benchmark bytecode and is not part of this audit.

Some vendored upstream Solidity comments still mention the historical 0.7.6 compiler or link to
0.7.6 documentation; those comments are not the benchmark compiler pin.  The command above is the
artifact provenance for this benchmark.

Artifacts:

- `creation.hex`: optimized creation bytecode, 11788 bytes, sha256 `410cc595f77a67b48e84b33f35e98444217ff5265a9bf454f6115c1635efb3fc`
- `runtime.hex`: optimized deployed runtime bytecode, 11755 bytes, sha256 `0e4f8a6acc3ca0e7240cafb99580e33dee7d2c7d3fff49cc88df6cea664a4fcd`
- `Safe.abi.json`: ABI emitted by solc, sha256 `40069244550920fc4ecdb4a162f9b45c78b5de06fc7fdcb8f7d4350739bb8682`
- `sources.sha256`: sha256 manifest for the vendored Solidity source tree
- `Spec.lean`: Stele AST with ABI surface, solc 0.8.35 decoding, and physical storage layout
- `SpecSyntax.lean`: syntax-side wrapper checked definitionally against the AST scaffold
- `Bytecode.lean`: optimized bytecode embedded as `ByteArray`, with `valid_jumps` facts
- `Constructor.lean`: proved constructor equivalence
- `Correct.lean`: proved runtime and whole-contract refinement
- `CorrectProofAudit.lean`: checks the constructor, runtime, and whole-contract axiom footprints
- `Runtime.lean`: 33 proved entrypoint obligations (31 selectors, receive, fallback)
- `Blocks.lean`, `Blocks/`: generated runtime and constructor instruction summaries and PC indexes
- `ArtifactChecks.lean`: executable checks of every ABI signature, selector, and return type
- `Audit.lean`, `AuditSupport.lean`: differential regressions against the actual EVM interpreter
- `AuditManifest.json`: reproducible compiler, ABI, storage, instruction, event, and boundary inventory

Main source sha256: `1ffd10dbcb76e9983e5dd40bc230d71aa3dfc231165176bbac9596513137af4e`.

## Semantic audit

The audit target is the pinned bytecode under the repository's current `Stele.runtimeRefinement`.
That relation observes the final account map, successful return bytes, reverts, invalid-instruction
halts, and static-mode violations. Gas exhaustion has its own refinement case. Gas observations
and call gas/substate inputs are existential witnesses. Log contents and revert payloads are not
observed. Consequently this is not a claim of equivalence for all observables of a production EVM.

The constructor and all runtime obligations are proved. The proofs handle gas exhaustion through
the refinement relation's out-of-gas cases and use the actual EVM call result for external calls.
No additional well-formed-storage, successful-decoding, nonstatic, or restricted-callee assumptions
were needed. The trusted base consists of Lean's standard axioms and concrete `native_decide`
evaluation facts; selector identities use kernel evaluation.

Corrections made during the audit:

| Area | Bytecode evidence and specification behavior |
| --- | --- |
| Events and static mode | All 17 `LOG` sites now have event statements in source order. Receive emits at PC 533. Setup emits at PC 4540 **before** its threshold/owner checks. Module events follow the post-guard; transaction events precede the post-guard. |
| Assembly address stores | PCs 5850, 6100, and 8575 perform whole-word `SSTORE` for module guard, guard, and fallback handler. Their locators now have size 32; ordinary address mappings retain 20-byte writes preserving unrelated high bits. |
| Fallback raw-word check | PCs 581–586 test the entire handler slot. A nonzero word with zero low 160 bits still calls address zero. The spec reads the raw word before converting the call target to an address. |
| Allocation panics | The explicit `new` size guards for owners, module pages, and raw storage bytes are retained. `getStorageAt` checks the wrapped `length << 5`, not unbounded multiplication. |
| Memory argument decoding | The decoder at PC 9121 checks its new free-memory pointer. Its sole memory `bytes` argument starts at 0x80, so `0x80 + 32 + ceil32(length) <= 2^64 - 1` requires `length <= 2^64 - 192`. All eight affected entrypoints now check this; calldata-only arguments do not. |
| Signature dispatch | There is no P-256 branch. Values other than 0, 1, or greater than 30 use ordinary ecrecover, including `v = 2`. |
| Contract signatures | The `STATICCALL` at PC 7249 propagates failure. The return decoder at PC 11600 accepts at least 32 bytes, validates canonical `bytes4` padding, and permits trailing data. |
| Self owners | Setup, add, and remove reject only zero/sentinel owner addresses. Swap also rejects a new owner equal to this Safe. The EIP-7702 code probe is absent. |
| Execution order | Nonce increment precedes transaction hashing, as in the `nonce++` argument evaluation. Raw storage slot addition is explicitly reduced to 256 bits. |

The remaining behavior was checked against the vendored sources, the exactly reproduced compiler
output, its generated ABI decoder code, and source-mapped instructions:

| Surface | Checks retained |
| --- | --- |
| Dispatcher, receive, fallback | All 31 selectors, short and unknown selectors, per-entrypoint payability, decoding failures, empty calldata, caller suffix, raw success return, and propagated call failure. |
| Owner management | Authorization, sentinel and zero restrictions, swap self-address restriction, duplicate owners, linked-list rewiring, checked count changes, threshold updates, malformed lists and array bounds. |
| Module management | Enable/disable authorization, sentinel membership, page allocation and truncation, last-element continuation, broken zero links, cached guard, call/delegatecall distinction, return-data capture before post-guard. |
| Setup and constructor | Constructor writes only threshold after its value check. Setup event order, single initialization, owner setup, full-word fallback store, code-existence check for setup delegatecall, and optional payment. |
| Signatures | Both compatibility overloads, ignored data preimages, checked `requiredSignatures * 65`, ordered owners, all `v` branches, dynamic bounds and overflow checks, approved hashes, typed ERC-1271 magic/return decoding and propagated failure, ordinary ecrecover for `v = 2`, ecrecover failure. |
| Transaction and payment | EIP-712 constants/encoding, nonce timing, enum validation, guard checks, checked additions and wrapping shift in gas check, failure policy, native refund price cap/origin, ERC-20 empty/32-byte/nonzero acceptance, and event/post-guard ordering. |
| Views and simulation | Scalar and mapping getters, flattened tuple returns, domain/transaction hashes, modulo raw storage addressing, delegatecall effects followed by unconditional revert. |
| Calls | Correct caller/value/permission inheritance, depth and balance failures, arbitrary target code, raw return data, typed bool validation, missing code on void calls, and callee world effects. |

`Audit.lean` runs every selector in both permission modes and with zero/nonzero call value, then
checks malformed ABI heads, dirty storage, linked lists, calldata aliases, guard return sizes,
contract signatures, removed P-256 inputs, self owners, token return conventions, refunds, delegatecall storage changes,
depth limits, and construction. It compares success return bytes and the entire final account map.
Call replay also checks opcode, target, value, calldata, and the account map before every call.
The owner guards keep the proof’s pure helper factorization; checks before the first storage write
are equivalent to the inlined source guards. Contract-signature validation uses a helper for the
typed call and magic-value comparison.
The harness reports out-of-gas separately and fails on test-fuel exhaustion or unsupported AST
forms. It is independent of the refinement proofs.

The recorded regression run passed all 414 cases: 107 successes, 295 reverts, 11 static-mode
violations, and one separately classified out-of-gas result. The targeted Lake build includes
the specification equality check, ABI checks, refinement proofs, and all generated summaries.

## Generated summaries and proof obligations

There are 1,920 runtime summary theorems in 51 shards, plus seven constructor summary theorems.
These are generated using the existing RD opcode lemmas. Both sides of every conditional jump
are indexed. Runtime summaries cover 7,738 instructions; the remaining 18 instruction sites are
explicit boundaries, not assumed transitions:

- `CALL`: 614, 3644, 4141, 7513, 7632, 7733, 8002, 8901.
- `STATICCALL`: 2460, 2557, 5739, 5989, 7249.
- `DELEGATECALL`: 4441, 7613.
- `ORIGIN`: 7922.
- `GASPRICE`: 7943, 7950.

Every analyzed instruction is accounted for by a summary or a recorded boundary. Constructor
summaries cover only PCs 0–32; the runtime at offset 33 is copied data. They quantify an arbitrary
constructor-argument tail against the full creation bytecode. Solidity CBOR metadata is excluded
from runtime instruction analysis. Summary hypotheses such as valid jump destinations, stack
bounds, and static permission are discharged in the entrypoint proofs. Shared routine proofs
compose the summaries, with separate proofs for internal callees and source-level call wrappers.

## Reproduction and validation

From the repository root, using the pinned compiler:

```bash
python3 -B scripts/audit_safe.py --dir Benchmarks/Safe/V0_cdb2eb5 --solc /path/to/solc-0.8.35
lake build Benchmarks.Safe.V0_cdb2eb5.ArtifactChecks Benchmarks.Safe.V0_cdb2eb5.SpecSyntax
lake build Benchmarks.Safe.V0_cdb2eb5.Correct Benchmarks.Safe.V0_cdb2eb5.Audit
lake build Benchmarks.Safe.V0_cdb2eb5.CorrectProofAudit Benchmarks.Safe.V0_cdb2eb5.GetOwnersModelAudit
lake env lean Benchmarks/Safe/V0_cdb2eb5/Audit.lean
```

The Python check recompiles source, verifies every source hash and both Lean byte arrays, checks
the ABI/dispatcher agreement, and checks that generated files match their current generator.
Add `--write` to regenerate summaries, indexes, ABI checks, and the manifest. It does not fill
refinement proofs. The SHA-256 values in the artifact list above hash the **hex text files**;
the manifest separately records hashes of the decoded bytecode bytes.

The randomized differential test reports:

```text
Safe_V0_cdb2eb5: 1775 cases: 1760 agree (579 successful), 0 disagree, 0 stuck, 15 EVM out of gas, 0 spec out of fuel
```

The EVM dependency's Python cryptography helpers resolve paths from its package directory.
Install its declared `requirements.txt` in a virtual environment, add that environment's `bin`
directory to `PATH`, and run the randomized suite there (with `-d` pointing to this repository):

```bash
cd .lake/packages/evmlean
lake -d ../../.. exe stele-difftest --only Safe_V0_cdb2eb5 --count 50
```
