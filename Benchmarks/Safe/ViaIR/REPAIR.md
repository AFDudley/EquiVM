# Safe via-IR repair status

The port is incomplete. Artifact regeneration and the semantic gates passed; constructor and
shared dispatcher repairs build. The remaining runtime proofs and whole-contract axiom audit
have not been repaired or verified.

Solc `0.8.35+commit.47b9dedd`, with only `--via-ir` added, produces an 11,003-byte runtime and
11,034-byte creation program. The constructor prelude shrinks from 33 to 31 bytes and copies
the runtime into memory at 128 instead of 0. The binary dispatcher becomes a linear selector
chain starting at PC 168, retaining an additional zero word on the stack. Receive and fallback
precede that chain; external bodies are inlined and internal routines are reorganized. There
are 1,871 runtime summary theorems in 49 shards, 6,974 summarized instructions, and 26 explicit
boundaries, compared with 1,937, 51, 7,844, and 20 in the legacy baseline.

The regression audit reports 408 cases and `failures 0`, with unchanged outcome counts. Its
four gas-observation PCs were updated from the compiler source map; no expected outcomes or
specifications changed. The randomized summary is:

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
33 entrypoint refinement statements remain unchanged. The constructor axiom check reports only
`propext`, `Classical.choice`, `Quot.sound`, and native-decide certificates. No proof holes or
custom axioms were added.

The current blocker is generated `safeRuntime_block_4770`, whose gas-counter normalization
hits Lean's default recursion limit at `Blocks/Runtime_023.lean:330`. The unchanged shard passes
with `lake env lean -DmaxRecDepth=10000 Benchmarks/Safe/ViaIR/Blocks/Runtime_023.lean`.
An isolated generator proposal also emits a shard that passes with the default Lean command.
It adds an optional recursion limit to the block renderer and enables 10,000 only for the
Safe audit's `--via-ir` runtime output. Default generation was checked byte-for-byte unchanged;
the IR proposal only adds the option and updates index line numbers. The proposed patch is
saved at `/tmp/safe-viair-generator-recdepth.patch` and has not been applied.

The prescribed artifact audit currently passes without `--write`, but it compares generated
text exactly, so manually adding the option to a shard would fail that check. Applying the
proposal requires a scope exception for `scripts/generate_rd_blocks.py` and `scripts/audit_safe.py`.
The compiler-port instructions forbid those edits and require stopping to report them. `Main`,
the source tree, source manifest, specifications, and shared libraries remain untouched.
