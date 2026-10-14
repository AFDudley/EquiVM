# Safe optimizer-runs repair

The port uses Solidity `0.8.35+commit.47b9dedd`, changing only optimizer runs from
200 to 1,000,000. Runtime size grew from 11,874 to 14,838 bytes; creation size is
14,871 bytes. The summaries show precomputed address masks, rounding masks, and
shifted constants emitted as larger `PUSH` literals, eliminating arithmetic
instructions. This relocates PCs and merges or moves some summary boundaries.
The bytes allocator reorders its rounding and overflow checks and needs one extra
stack slot. The checked increment tests subtraction of `2^256 - 1`; the guard
encoders also change stack scheduling and operand order. The regenerated runtime
inventory covers 7,263 summarized instructions and 20 explicit boundaries in 51 shards.

The Solidity sources and both specifications are unchanged. All 33 entrypoint
refinement statements, `safeCorrect`, `safeConstructorCorrect`, and
`safeContractCorrect` are unchanged. Internal trace statements relocate PCs and
generated-summary references. Other statement changes are:

| Lemmas | Change and reason |
| --- | --- |
| `safeCreationRuntime` | Runtime copy length 11,874 → 14,838. |
| `safeStorageAtLengthCheck` | Exact step/gas increments `(17, 55)` → `(13, 43)` after constant folding. |
| `safeDecodeMemoryBytesOrRevert`, `safeDecodeMemoryBytesValid`, `safeDecodeMemoryBytesEvidence` | Stack allowance 10 → 11 for the reordered allocator. |
| `safeDecodeAddressMemoryBytesOrRevert` | Stack allowance 16 → 17, propagated from the bytes decoder. |
| `safeDecodeModuleArgsValid`, `safeDecodeModuleArgsEvidence` | Stack allowance 18 → 19 for the same reason. |
| `safeDecodeSignatureAddressValid`, `safeDecodeSignatureAddressEvidence`, `safeDecodeSignatureAddressTooLarge` | Stack allowance 18 → 19 for the same reason. |
| `safeSimulateReverts` | Stack allowance 17 → 18 for its decoder call. |

The proof structure and existing declarations were retained. Most repairs are PC,
summary-composition, literal-normalization, or execution-counter updates. Local
equalities establish the new literal masks, increment test, and allocation
expression. The generated removal summary now crosses the existing link-update
checkpoint, so `safeRemoveOwnerLinksTrace`, `safeRemoveOwnerThresholdUnchanged`,
and `safeRemoveOwnerThresholdChanged` re-establish those segments from opcode
lemmas within their existing proofs. Module enable/disable, owner swap, and token
transfer compose the newly merged or split summaries; static-store traces use
the new pushes. No entrypoint proof was replaced wholesale, and no proof modules
were added or removed.

The required four-target Lake build and artifact reproduction check both passed.
The differential audit passed 408 cases: 292 reverts, 104 successes, 11 static
violations, and one out-of-gas result, with zero failures. The randomized result was:

```text
Safe_Runs1e6: 1775 cases: 1762 agree (579 successful), 0 disagree, 0 stuck, 13 EVM out of gas, 0 spec out of fuel
```

The randomized run used a temporary Python environment and wrapper to resolve the
bundled precompile scripts and their dependencies; repository support code was
unchanged. `#print axioms` for `safeContractCorrect` reports only `propext`,
`Classical.choice`, `Quot.sound`, and 11,056 `native_decide` certificates. The
constructor, runtime, transaction body, and whole-contract axiom audit found no
unexpected axioms. There are no `sorry`, `admit`, or new axiom declarations.

Blockers: none.
