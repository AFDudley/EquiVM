# Pipeline validation runs

Complete runs of the scaffold automation (`Misc/scaffold-prompt.md`) on contracts written for it.
Every file but the sources, `SpecSyntax.lean` and `HANDOFF.md` is generated (each `HANDOFF.md`
lists its hand edits); regenerate with the commands recorded there. The directories build (`lake build Tests.Pipeline.<Name>.Correct`)
with exactly the generated `sorry` stubs, and their targets run in `lake exe stele-difftest`.

- `Vault/`: immutables set by a constructor with arguments, modifiers, a transient reentrancy
  lock (EVM version cancun), a mapping, a dynamic array with push and pop, typed external calls
  with return values, events.

Vyper runs (`scripts/vy2stele.py` drafts, the Vyper mode of `scripts/proof_skeleton.py` writes
the skeleton with a proved jump-table dispatcher; `lake build Tests.Pipeline.Vyper<Name>.Correct`
succeeds with the generated stubs, which for contracts with immutables include `deployed_of_fit`
in `Common.lean`):

- `VyperVault/`: a payable deposit with a fee, `send`-based withdrawals under
  `@nonreentrant` (EVM version shanghai: the lock is storage slot 0), an immutable owner,
  getters.
- `VyperRegistry/`: an `initializes`/`exports` module, a default argument (two selectors), a
  bounded `DynArray` state with `append`/`pop` (`vyperBoundedStorage!`), a struct mapping with
  its getter, a loop over the array, events.
- `VyperWrapper/`: `extcall`/`staticcall` to an ERC20 interface held in an immutable, a call
  without return data guarded by `EXTCODESIZE`, checked arithmetic with division, events.
