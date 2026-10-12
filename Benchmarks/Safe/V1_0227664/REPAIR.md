# Safe proof repair

Ported `Main` from upstream `77901a5a1ad835b74ad3b72f73a8412cfe491c57` to
`cdb2eb578dbdba4c3f10a47f9a2dd9580773e63a`. The vendored sources reproduce with
`0.8.35+commit.47b9dedd`, optimizer 200, Shanghai, and metadata hash disabled:
11,755 runtime bytes and 11,788 creation bytes. The source and artifact hashes are
recorded in the benchmark provenance.

The specification changes follow three bytecode changes:

- Signature dispatch has no P-256 branch. After the `v = 1` test at PC 2200,
  PC 2301 tests `v > 30`; `v = 2` now reaches ordinary ecrecover.
- Owner validation no longer probes EIP-7702 delegation code. Setup, add, and
  remove permit the Safe itself as an owner, subject to the remaining address
  and linked-list checks. The inlined guards start at PCs 8252, 1744, and 6729.
  Swap retains a separate new-owner/self check at PCs 6162–6234.
- Contract signatures use the typed ERC-1271 call at PC 7249. Failure reverts
  through PCs 7250–7257. The decoder at PC 11600 requires at least 32 return
  bytes; PC 11616 checks zero padding after the first four bytes. Trailing data
  is accepted. PC 7300 compares the decoded value with `0x1626ba7e`.

The spec retains pure owner-guard helpers and a contract-signature helper as
factoring of the inlined code. The syntax/AST equality remains proved. Before
proof repair, the deterministic audit passed all 414 cases with `failures 0`;
the differential test with seed 2026 and `--count 50` reported:

```text
Safe_V0_cdb2eb5: 1775 cases: 1760 agree (579 successful), 0 disagree, 0 stuck, 15 EVM out of gas, 0 spec out of fuel
```

All 33 `safe…Refines` statements and `safeConstructorCorrect`, `safeCorrect`, and
`safeContractCorrect` are unchanged. Most helper edits only relocate PCs and
jump destinations; constructor copying now uses the new runtime length.
The substantive helper-statement changes are:

- `safeValidOwnerTrace` / `safeInvalidOwnerTrace`, `safeCanAddOwnerHeapTrace*`,
  `safeCanAddOwnerTrace*`, and `safeCanRemoveOwnerTrace*` describe the inlined
  guard stacks and memory effects. Swap source lemmas take the separate
  new-owner/self inequality; new trace lemmas cover its distinct guard sites.
- `safeByteBufferCopyLoopAfter`, `safeByteBufferCopyLoopInto`,
  `safeByteBufferCopyLoop`, and `safeWordBufferCopyLoop` use buffer-header
  pointers and the extra loop stack word introduced by the compiler's inlined
  bytes-copy loop.
- `safeContractSignatureArgs`, `safeContractSignatureEncode`,
  `safeContractSignaturePrepare`, `safeContractSignatureReturnBuffer`,
  `safeContractSignatureFinish`, and `safeContractSignatureTrace` describe the
  direct argument buffer, 32-byte output window, typed decoder, and revert
  alternatives. Their memory lemmas reflect the new free-pointer update and
  require the relevant pointer/return-size bounds. `evalContractSignatureResult`,
  `safeContractSignatureSource`, `safeCheckContractCall`, and
  `safeCheckContractSource` now handle typed-call and decoding failure.

The owner guards, setup-owner iteration, bytes-copy loop, and contract-signature
call/return paths required new traces within the existing proof structure.
The new `bytes4` decoder is proved against both the EVM mask and the ABI padding
check. Argument copying accounts for header writes overlapping only the unused
padding of the final source word. Proofs solely for the removed P-256,
delegation-probe, and duplicate call-buffer-copy paths were removed.

Final validation passed the combined build of `Correct`, `CorrectProofAudit`,
`ArtifactChecks`, and `Audit` (3,907 jobs), and `audit_safe.py` without `--write`.
The artifact audit accounts for 7,738 summarized runtime instructions and 18
explicit boundaries in 51 shards. The explicit `#print axioms` for
`safeContractCorrect` contains `propext`, `Classical.choice`, `Quot.sound`, and
11,827 `native_decide` certificates, with no unexpected axioms. There are no
`sorry`, `admit`, or explicit new axioms in the target Lean sources.

No blockers remain. Changes outside the target are limited to its differential
test registry entry; `Main` and the shared semantics are unchanged.
