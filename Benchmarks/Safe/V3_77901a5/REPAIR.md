# Safe proof repair: 0e91d99 to 77901a5

Ported from `0e91d99ea35f2ec650dd7cb3795f78eeacec7985` to
`77901a5a1ad835b74ad3b72f73a8412cfe491c57`, using only the starting proof and
Solidity `0.8.35+commit.47b9dedd`. All 69 upstream contract files are byte-exact.
The regenerated runtime and creation bytecode contain 11,874 and 11,907 bytes.

## Specification and evidence

Contract signatures now use `SecuredSignatureValidator`: a low-level static call
returns a Boolean requiring call success, exactly 32 return bytes, and the entire
word equal to the zero-padded ERC-1271 magic value. Previously, the typed bytes4
decoder accepted trailing return data and reverted inside the helper on call or
decoding failure. The new helper returns `false`; its caller enforces `GS024`.

The bytecode performs `STATICCALL` at PC 8796, checks success and exact length at
PCs 8852–8871, decodes bytes32 at PC 11787, and compares the full word at PC 8903.
PC 7053 branches to the caller's `GS024` revert when the result is false.
The specification syntax equality remains proved.

Before proof edits, the deterministic audit passed 468 cases with `failures 0`.
The required randomized run (`--count 50`) reported:

```text
Safe_V3_77901a5: 1775 cases: 1761 agree (578 successful), 0 disagree, 0 stuck, 14 EVM out of gas, 0 spec out of fuel
```

## Proof changes

All 33 entrypoint refinement statements and the statements of `safeCorrect`,
`safeConstructorCorrect`, and `safeContractCorrect` are unchanged. For unchanged
code, statement edits only relocate program counters or update the creation
proof's embedded runtime length.

The four byte-buffer copy-loop statements now describe the factored loop's new
stack, cleanup address, and stack bound. Their induction proofs were adapted in
place. The ABI encoder's external memory result is preserved.

`evalContractSignatureResult`, `safeContractSignatureSource`, and
`safeCheckContractCall` now describe unconditional Boolean returns from the helper.
`safeContractSignatureArgs`, `safeContractSignatureEncode`,
`safeContractSignaturePrepare`, `safeContractSignatureCallFailure`,
`safeContractSignatureReturnBuffer`, `safeContractSignatureFinish`, and
`safeContractSignatureTrace` describe the new allocation, call, return-data, and
short-circuit paths. The trace additionally requires the zero slot and sufficient
space for the allocated return buffer. The existing caller discharges these
conditions without changing its statement.

The header-size, argument free-pointer, call-memory size/free/read, and final-memory
size statements follow the new allocation layout. Other memory preservation and
growth guarantees remain intact. Obsolete bytes4 decoder trace lemmas,
`contractSignatureResult_of_not_decoded`, and `contractSignatureNext_word` were
removed with their replaced paths.

The secured helper could not be repaired by relocation alone: its selector patch,
second byte copy, raw return-data allocation, exact-word check, and caller require
were reproved. New support for the second copy covers its overlapping final
partial-word load and cleanup; only actual payload bytes are used. Existing
arithmetic, ABI, memory, static-call, and bytes32-decoder proofs were reused.

## Final verification

The required joint build of `Correct`, `CorrectProofAudit`, `ArtifactChecks`, and
`Audit` succeeds; the audit again reports `failures 0`. Artifact verification
without `--write` reproduces the pinned compilation and all summaries.
There is no `sorry`, `admit`, or axiom declaration in the target Lean sources.
`#print axioms safeContractCorrect` reports only `propext`, `Classical.choice`,
`Quot.sound`, and 11,925 native-decision certificates; the proof audit reports no
unexpected axioms. Repository edits are confined to the target and its registry
entry. Blockers: none.
