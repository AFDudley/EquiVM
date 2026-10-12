# scripts/ — scaffold and proof-skeleton automation

Everything a proof needs that is a pure function of the compiler artifacts is generated here.
The agent's work starts after these scripts: closing the spec holes, auditing the spec against
the bytecode report, and proving the function bodies.

All scripts are plain Python 3 with no third-party Python dependencies (keccak is included), run
from the repository root. `solc` binaries are taken from `--solc`; the standard-JSON interface is
used, so any solc ≥ 0.5 works. Vyper compilation uses a Vyper 0.4.3 executable passed to
`--vyper` and a pinned local import tree.

## Pipeline for a new contract

```bash
D=Benchmarks/Scaffolds/Foo        # contract directory; sources under $D/contracts/
M=Benchmarks.Scaffolds.Foo        # its Lean module path

# 1. compile and pin the artifacts (runtime/creation hex, ABI, storage layout, AST, build json)
scripts/scaffold.py compile --dir $D --solc /path/to/solc-0.8.20 --main contracts/Foo.sol \
    --contract Foo --runs 200 --evm-version shanghai --metadata-hash none

# 2. Bytecode.lean (chunked bytes + JUMPDEST theorems), Selectors.lean (table + keccak facts),
#    Immutables.lean / ImmutableCode.lean for contracts with immutables
scripts/scaffold.py lean --dir $D --module $M

# 3. proved block summaries for the runtime and the creation code
scripts/scaffold.py blocks --dir $D --module $M

# 4. the bytecode report: census, dispatcher, source functions, routines, annotated blocks
scripts/bytecode_report.py $D -o $D/REPORT.md

# 5. the spec draft (holes fail to elaborate until closed; --comment-holes to check the rest)
scripts/sol2solm.py $D --namespace $M -o $D/SpecSyntax.lean --spec-json $D/Foo.spec.json

# 6. the proof skeleton: Spec, Common, Dispatch (proved), <Fn>.lean stubs, Constructor, Correct
scripts/proof_skeleton.py --dir $D --module $M

# 7. consistency checks, and the finish checklist once the proof is done
scripts/scaffold.py check --dir $D
scripts/finish_check.py --dir $D --module $M --theorem $M.fooContractCorrect
```

`scaffold.py all` runs steps 1–3 and the check in one go. Steps 2, 3 and 6 never overwrite existing
files unless `--force` is given.

## Vyper path

Put the exact main `.vy`, imported `.vy`/`.vyi` files, and any imported package modules under
`<Dir>/contracts/`, preserving their import paths. Pin the compiler and EVM fork:

```bash
scripts/scaffold.py all --dir <Dir> --vyper /path/to/vyper-0.4.3 \
    --main path/to/Main.vy --contract Main --evm-version prague --module <Module>
scripts/bytecode_report.py <Dir> -o <Dir>/REPORT.md
```

`all` generates artifacts, Lean bytecode, selectors, block summaries, and a differential target.
The build JSON records the source `# pragma optimize` mode, including `codesize`. The report uses
Vyper's `pc_pos_map` for block-to-source line annotations; solc AST function ranges are unavailable.
Check the source and `<Name>.storage.json` together before writing `SpecSyntax.lean`.

`sol2solm.py` requires a solc AST, so write a Vyper `SpecSyntax.lean` manually. Use
`Examples/VyperERC20/SpecSyntax.lean` for the Solm syntax and include a transition for every ABI
selector, including variants from default arguments. Once it builds, generate the Config shell:

```bash
scripts/proof_skeleton.py --dir <Dir> --module <Module> --only Spec
lake build <Module>.Spec
```

This selects the static Vyper storage backend and Vyper calldata mode. For bounded dynamic state,
replace `vyperStorage!` with source-checked `vyperBoundedStorage!` declarations. For bounded
entry arguments, replace `.withMode DecodeMode.vyper` with `.withVyperABI` and list the
capacity-bearing selector variants from the source; ABI JSON does not retain their bounds.
Review explicit `abi_decode`, constructor inputs, and return decoding separately. If a contract
uses Vyper transient state, write its backend explicitly; `proof_skeleton.py` will stop instead
of generating a Solidity transient layout.

The full `proof_skeleton.py` dispatcher, constructor, and immutable templates currently assume
solc bytecode. It therefore accepts only `--only Spec` for Vyper. Use `Examples/VyperERC20` for a
complete Vyper proof and `Examples/VyperImmutable` for generated immutable suffix artifacts;
write the remaining proof modules against the generated block summaries. A successful `all` run
is an artifact scaffold, not a finished ready-to-prove contract skeleton.

## What each script produces

| Script | Output | Notes |
|---|---|---|
| `scaffold.py compile` | `runtime.hex`, `creation.hex`, `<Name>.abi.json`, `<Name>.storage.json`, `<Name>.build.json`, `sources.sha256`; solc also emits `<Name>.sol.ast.json` and `<Name>.metadata.json` | `build.json` holds compiler settings and selectors. Solc includes AST and immutable patch sites; Vyper includes its source maps and code-layout immutables. |
| `scaffold.py lean` | `Bytecode.lean`, `Selectors.lean`, `Immutables.lean`, `ImmutableCode.lean` | Selector table in `SpecSyntax.lean` order when that file exists, else by selector value. Selector facts are spec-independent keccak facts; the bridge to each transition is in the skeleton's `Common.lean`. |
| `scaffold.py blocks` | `RuntimeBlocks_NNN.lean`, `CreationBlocks_NNN.lean`, `.index` files | `generate_rd_blocks.py` driven with the right code terms, immutable-aware when needed. |
| `scaffold.py check` | report | Lean bytes vs hex, jump tables vs the EVM scan, selector table vs ABI and spec order, immutable offsets, source hashes. |
| `scaffold.py difftest` | `DiffTarget.lean`, `Tests/DiffTest/Generated.lean` | The contract's `Target` for the differential suite (spec, config, runtime, creation code, immutable plumbing when the contract has immutables) and the registry of every `DiffTarget.lean` in the repository, which `lake exe solm-difftest` runs. Delete a `DiffTarget.lean` and rerun to unregister. |
| `bytecode_report.py` | Markdown | Opcode census, dispatcher, JUMPDEST set and annotated blocks. Solc reports AST function ranges and internal routines; Vyper reports source lines from `pc_pos_map`. |
| `sol2solm.py` | `SpecSyntax.lean` draft, optional `.spec.json` | From the solc AST: storage (persistent and `transient`)/structs/events/immutables, constructor with base constructors and initialisers inlined, external functions (modifiers inlined, getters generated), reachable internal and library functions, checked arithmetic from static types, external calls bound with view flags and EXTCODESIZE guards, via-IR calldata guard. Holes for what it cannot translate. |
| `proof_skeleton.py` | Solidity: `Spec.lean`, `Common.lean`, `Dispatch.lean`, `<Fn>.lean`, `Constructor.lean`, `Correct.lean`; Vyper: `Spec.lean` with `--only Spec` | The full proof template uses solc dispatch and immutable assumptions. Vyper `Spec.lean` selects Vyper storage and ABI defaults, then needs capacity review. |
| `check_sol2solm.py` | report | Translates every given directory and elaborates the drafts (holes as comments). |
| `finish_check.py` | report | Build, differential suite on the contract (`--difftest-count`, `--skip-difftest`), `sorry`/`admit`/`axiom` grep, `#print axioms` against the accepted trusted base. |
| `check_all_benchmark_blocks.py` | report | Check that benchmark block summaries compile, excluding temporary contracts under `Benchmarks/Scaffolds/`. CI selects `UniswapV3/Pool`. |

## Conventions the generators follow

- Transition order is the `SpecSyntax.lean` function order; the translator writes them in selector
  order, which is the compiled dispatcher order.
- Declarations are prefixed with the lowerCamel contract name (`fooBytecode`, `fooSelBytes`,
  `fooReachTransferBody`, `fooTransferBody`); overloaded functions get their parameter types
  appended (`file_bytes32_uint256`).
- Constants are inlined at their uses (solc does the same; the surface grammar has no constant
  item). Enums are `uint8`. Interface casts are dropped (receivers are addresses).
- A public function that is also called internally is split into `<f>_body` (internal) plus the
  external wrapper, so the internal call does not pass through the entry guards.
- Internal `storage` parameters and returns keep their source types, including mappings and
  library structs. Named storage returns and local pointer assignments bind aliases. Library
  extension calls include their receiver; colliding struct names are qualified by their owner.
- Memory structs, arrays, `bytes` and `string` are passed to internal functions by reference in
  Solidity but by value in Solm. A callee that may modify one (directly, or through a callee)
  returns its final value after the declared results, and the caller assigns it back to the
  argument's path. Overlapping arguments, a parameter that is reassigned and modified, and a
  modification through a local alias of a parameter are holes.
- Contracts with a `fallback`/`receive` get `sorry` stubs for the Solm dispatch facts: the
  unmatched-selector path then runs the fallback instead of reverting.

## Tests

```bash
python3 scripts/test_generate_rd_blocks.py
python3 scripts/test_scaffold_tools.py
```

`Misc/scaffold-prompt.md` is the agent brief that runs these scripts from a contract to a
ready-to-prove scaffold.

The differential suite (`lake exe solm-difftest`, `Tests/DiffTest/README.md`) runs every
specification against its bytecode.  `scaffold.py difftest` registers a contract; once its
specification compiles, `lake exe solm-difftest --only <Name> --count 50` tests it before any
proof is attempted, and `finish_check.py` runs it again at acceptance.
