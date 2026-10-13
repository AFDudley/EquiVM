# Safe Benchmark

Source: [`contracts/Safe.sol`](contracts/Safe.sol) from `safe-global/safe-smart-account` commit `77901a5a1ad835b74ad3b72f73a8412cfe491c57` (2026-06-05, `Do Not Propagate Reverts on Signatures (#1115)`).

Compiled with Solidity 0.8.35 through the IR pipeline and optimizer enabled, from the repository root:

```bash
solc --via-ir --optimize --optimize-runs 200 --evm-version shanghai --metadata-hash none --bin --bin-runtime --abi --storage-layout \
  --base-path . --overwrite -o /tmp/safe-viair-build Benchmarks/Safe/ViaIR/contracts/Safe.sol
```

Compiler: `0.8.35+commit.47b9dedd.Linux.g++`. Only `--via-ir` differs from the
legacy compiler settings. The audit reproduces both bytecode files and the ABI exactly.

The EVM target is pinned to Shanghai to reproduce the original artifacts. The current local
EVM semantics also implement `MCOPY`; changing the compiler target would still change the
benchmark bytecode and is not part of this audit.

Some vendored upstream Solidity comments still mention the historical 0.7.6 compiler or link to
0.7.6 documentation; those comments are not the benchmark compiler pin.  The command above is the
artifact provenance for this benchmark.

Artifacts:

- `creation.hex`: optimized creation bytecode, 11034 bytes, sha256 `60f584185471210453fd3e9aa6f4f994daf1eec6465f5b5cd3ed3457d966fa26`
- `runtime.hex`: optimized deployed runtime bytecode, 11003 bytes, sha256 `01ed7613d9170c16d92505d5db5eb71ad2179f9b0435a3bb077b7f4b71833f97`
- `Safe.abi.json`: ABI emitted by solc, sha256 `40069244550920fc4ecdb4a162f9b45c78b5de06fc7fdcb8f7d4350739bb8682`
- `sources.sha256`: sha256 manifest for the vendored Solidity source tree
- `Spec.lean`: Solm AST with ABI surface, solc 0.8.35 decoding, and physical storage layout
- `SpecSyntax.lean`: syntax-side wrapper checked definitionally against the AST scaffold
- `Bytecode.lean`: optimized bytecode embedded as `ByteArray`, with `valid_jumps` facts
- `Constructor.lean`: proved constructor equivalence for the IR bytecode
- `Correct.lean`: runtime and whole-contract refinement targets, pending IR repair
- `CorrectProofAudit.lean`: checks the constructor, runtime, and whole-contract axiom footprints
- `Runtime.lean`: 33 entrypoint obligations (31 selectors, receive, fallback)
- `Blocks.lean`, `Blocks/`: generated runtime and constructor instruction summaries and PC indexes
- `ArtifactChecks.lean`: executable checks of every ABI signature, selector, and return type
- `Audit.lean`, `AuditSupport.lean`: differential regressions against the actual EVM interpreter
- `AuditManifest.json`: reproducible compiler, ABI, storage, instruction, event, and boundary inventory

Main source sha256: `9f91d9250e18bb0710b7b1f10dcbe2417e9ef8d22eeee98dba2ef48661a060fa`.

## Legacy baseline semantic audit

The following records the copied legacy proof and audit. Its PCs refer to the legacy bytecode,
not the regenerated IR artifacts. The IR regression audit also passes all 408 cases with the
same outcome counts. The randomized IR test reports 1,775 cases: 1,761 agree (578 successful),
0 disagree, 0 stuck, 14 EVM out of gas, and 0 spec out of fuel. The constructor and shared
dispatcher proofs have been repaired; runtime proof repair remains incomplete. See
[`REPAIR.md`](REPAIR.md) for the current repair status and a certified counterexample at a
symbolic calldata length of `2^255 + 4`. The unchanged runtime correctness statement is false
at that size. These executable tests do not establish correctness of the IR bytecode.

The audit target is the pinned bytecode under the repository's current `Solm.runtimeRefinement`.
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
| Events and static mode | All 17 `LOG` sites now have event statements in source order. Receive emits at PC 533. Setup emits at PC 4634 **before** its threshold/owner checks. Module events follow the post-guard; transaction events precede the post-guard. |
| Assembly address stores | PCs 5944, 6194, and 8317 perform whole-word `SSTORE` for module guard, guard, and fallback handler. Their locators now have size 32; ordinary address mappings retain 20-byte writes preserving unrelated high bits. |
| Fallback raw-word check | PCs 581–586 test the entire handler slot. A nonzero word with zero low 160 bits still calls address zero. The spec reads the raw word before converting the call target to an address. |
| Allocation panics | The explicit `new` size guards for owners, module pages, and raw storage bytes are retained. `getStorageAt` checks the wrapped `length << 5`, not unbounded multiplication. |
| Memory argument decoding | The decoder at PC 9242 checks its new free-memory pointer. Its sole memory `bytes` argument starts at 0x80, so `0x80 + 32 + ceil32(length) <= 2^64 - 1` requires `length <= 2^64 - 192`. All eight affected entrypoints now check this; calldata-only arguments do not. |
| Signature short circuit | The P-256 signer-address comparison precedes the precompile call. A mismatched address reverts without invoking the target. |
| Execution order | Nonce increment precedes transaction hashing, as in the `nonce++` argument evaluation. Raw storage slot addition is explicitly reduced to 256 bits. |

The remaining behavior was checked against the vendored sources, the exactly reproduced compiler
output, its generated ABI decoder code, and source-mapped instructions:

| Surface | Checks retained |
| --- | --- |
| Dispatcher, receive, fallback | All 31 selectors, short and unknown selectors, per-entrypoint payability, decoding failures, empty calldata, caller suffix, raw success return, and propagated call failure. |
| Owner management | Authorization, sentinel and zero restrictions, EIP-7702 three-byte code probe, duplicate owners, linked-list rewiring, checked count changes, threshold updates, malformed lists and array bounds. |
| Module management | Enable/disable authorization, sentinel membership, page allocation and truncation, last-element continuation, broken zero links, cached guard, call/delegatecall distinction, return-data capture before post-guard. |
| Setup and constructor | Constructor writes only threshold after its value check. Setup event order, single initialization, owner setup, full-word fallback store, code-existence check for setup delegatecall, and optional payment. |
| Signatures | Both compatibility overloads, ignored data preimages, checked `requiredSignatures * 65`, ordered owners, all `v` branches, dynamic bounds and overflow checks, approved hashes, exact ERC-1271 magic and 32-byte length, P-256 hash-derived address and exact result, ecrecover failure. |
| Transaction and payment | EIP-712 constants/encoding, nonce timing, enum validation, guard checks, checked additions and wrapping shift in gas check, failure policy, native refund price cap/origin, ERC-20 empty/32-byte/nonzero acceptance, and event/post-guard ordering. |
| Views and simulation | Scalar and mapping getters, flattened tuple returns, domain/transaction hashes, modulo raw storage addressing, delegatecall effects followed by unconditional revert. |
| Calls | Correct caller/value/permission inheritance, depth and balance failures, arbitrary target code, raw return data, typed bool validation, missing code on void calls, and callee world effects. |

`Audit.lean` runs every selector in both permission modes and with zero/nonzero call value, then
checks malformed ABI heads, dirty storage, linked lists, calldata aliases, guard return sizes,
contract signatures, P-256 results, token return conventions, refunds, delegatecall storage changes,
depth limits, and construction. It compares success return bytes and the entire final account map.
Call replay also checks opcode, target, value, calldata, and the account map before every call.
The harness reports out-of-gas separately and fails on test-fuel exhaustion or unsupported AST
forms. It is independent of the refinement proofs.

The recorded regression run passed all 408 cases: 104 successes, 292 reverts, 11 static-mode
violations, and one separately classified out-of-gas result. The targeted Lake build includes
the specification equality check, ABI checks, refinement proofs, and all generated summaries.

## Generated summaries and proof obligations

There are 1,871 runtime summary theorems in 49 shards, plus seven constructor summary theorems.
These are generated using the existing RD opcode lemmas. Both sides of every conditional jump
are indexed. Runtime summaries cover 6,974 instructions; the remaining 26 instruction sites are
explicit boundaries, not assumed transitions:

- `CALL`: 92, 4881, 5080, 5214, 5338, 5650, 9989, 10188, 10344, 10513, 10627.
- `STATICCALL`: 1637, 1928, 7776, 8460, 8678.
- `DELEGATECALL`: 3524, 3987, 4708, 10175.
- `ORIGIN`: 5002, 10450.
- `GASPRICE`: 5047, 5112, 10482.
- `EXTCODECOPY`: 10963.

Every analyzed instruction is accounted for by a summary or a recorded boundary. Constructor
summaries cover only PCs 0–30; the runtime at offset 31 is copied data. They quantify an arbitrary
constructor-argument tail against the full creation bytecode. Solidity CBOR metadata is excluded
from runtime instruction analysis. Summary hypotheses such as valid jump destinations, stack
bounds, and static permission are discharged in the entrypoint proofs. Shared routine proofs
compose the summaries, with separate proofs for internal callees and source-level call wrappers.

## Reproduction and validation

From the repository root, using the pinned compiler:

```bash
python3 -B scripts/audit_safe.py --dir Benchmarks/Safe/ViaIR --via-ir --solc /path/to/solc-0.8.35
lake build Benchmarks.Safe.ViaIR.ArtifactChecks Benchmarks.Safe.ViaIR.SpecSyntax
lake build Benchmarks.Safe.ViaIR.Correct Benchmarks.Safe.ViaIR.Audit
lake build Benchmarks.Safe.ViaIR.CorrectProofAudit Benchmarks.Safe.ViaIR.GetOwnersModelAudit
lake env lean Benchmarks/Safe/ViaIR/Audit.lean
lake exe solm-difftest --only Safe_ViaIR --count 50
```

The EVM dependency's Python precompiles resolve `Ethereum/EllipticCurvesPy/` relative to the
working directory and require `coincurve`, `pycryptodome`, and `typing-extensions`. If the root
command reports missing precompile scripts, run the built executable from `.lake/packages/evmlean`
with those Python dependencies on `PATH`. The recorded randomized result was also reproduced
there without precompile errors, using an isolated Python environment under `/tmp`.

The Python check recompiles source, verifies every source hash and both Lean byte arrays, checks
the ABI/dispatcher agreement, and checks that generated files match their current generator.
Add `--write` to regenerate summaries, indexes, ABI checks, and the manifest. It does not fill
refinement proofs. The SHA-256 values in the artifact list above hash the **hex text files**;
the manifest separately records hashes of the decoded bytecode bytes.
