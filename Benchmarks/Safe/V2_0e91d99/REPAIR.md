# Safe proof repair: 0227664 → 0e91d99

Ported upstream `02276647d5dd3353edc52d8c3e915f7f18dab95a` to
`0e91d99ea35f2ec650dd7cb3795f78eeacec7985` using the byte-exact upstream contracts and
Solidity `0.8.35+commit.47b9dedd`, with the original compiler flags.

The specification adds the `v = 2` P-256 signature branch and `p256Verify`. It checks that the
dynamic offset follows the static signatures and that the full 128-byte payload is available,
including checked-add overflow. It reads `(r, s, qx, qy)`, derives the signer from the low
160 bits of `keccak256(qx || qy)`, and validates the signature through address `0x100`.
Bytecode dispatch at PC 2209 selects this branch; PCs 2218–2387 implement its bounds, signer,
and validity checks. The `STATICCALL` at PC 7261 sends five words `(hash, r, s, qx, qy)`;
PCs 7262–7272 require call success and exactly 32 return bytes containing the word one.
The syntax/AST equality remains proved.

Before proof repair, the 468-case audit reported `failures 0`. The randomized differential run
with `--count 50` reported:

```text
Safe_V2_0e91d99: 1775 cases: 1761 agree (578 successful), 0 disagree, 0 stuck, 14 EVM out of gas, 0 spec out of fuel
```

All 33 `safe…Refines` statements and `safeContractCorrect`, `safeCorrect`, and
`safeConstructorCorrect` are unchanged. The 358 changed existing helper statements only
relocate instruction/return addresses and generated-summary references, or update bytecode
lengths: runtime 11499→11749 and creation 11532→11782. For example, `safeAddTrace` now enters
at PC 7193, and signature branch traces join at PC 2679. No existing declaration was removed.

Existing proofs were repaired in place; `signatureSwitchSource` and `safeSignatureBranchTrace`
were extended without changing their statements. The new P-256 path needed fresh proofs of
payload decoding, signer hashing, call/return behavior, and preservation of signature memory.
No existing proof required replacement.

All four required final Lake targets passed (3919 jobs), and the artifact audit passed without
`--write`. The final audit again reported 468 cases and zero failures. Source scans found no
`sorry`, `admit`, or custom axiom declarations. `#print axioms` and the complete axiom audit
confirmed only `propext`, `Classical.choice`, `Quot.sound`, and 11819 `native_decide` certificates
for `safeContractCorrect`.

Blockers: none.
