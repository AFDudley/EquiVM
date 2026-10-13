# Safe via-IR repair status

The port is incomplete. Artifact regeneration and the executable semantic gates passed;
constructor, shared dispatcher, and generated block summaries build. The huge-calldata
counterexample is addressed by a user-authorized decoder correction local to this benchmark.
The remaining runtime proofs and whole-contract axiom audit have not been completed.

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
Safe_ViaIR: 1775 cases: 1761 agree (578 successful), 0 disagree, 0 stuck, 14 EVM out of gas, 0 spec out of fuel
```

The prescribed root invocation printed this result but also reported missing Python precompile
support. The same built executable was rerun from the EVM dependency directory with an isolated
Python environment containing `coincurve`, `pycryptodome`, and `typing-extensions`; that run
completed with the same summary and no precompile errors.

Statement changes so far: `safeCreationRuntime` uses the new code offset, length, and memory
offset; `safeReachShort` reaches PC 14 instead of 475; `safeReachSelectorGroup` and `safeReachEntry`
retain the extra zero stack word. `safeSelectorStart` is now the constant PC 168. These describe
changed code. The constructor traces and selector-group proof were reproved in place, using the
new summaries and existing opcode lemmas. All three top-level correctness statements and all
33 entrypoint refinement declarations retain their text; `config` now incorporates the local
decoder correction described below. The constructor axiom check reports only
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
decoding mode or theorem input bound changed. The contract bodies and syntax spec are unchanged.

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
