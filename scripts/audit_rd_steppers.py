#!/usr/bin/env python3
"""Audit benchmark-local EVM steppers and branch-specific CALL proof overhead.

The report separates three notions that are easy to conflate:

* a semantic/RD gap evidenced by a local theorem over ``Xstep``;
* an old local workaround for which a canonical RD theorem now exists; and
* an RD-summary-generator gap in syntactically disassembled bytecode.

Only tracked Lean sources are inspected, so scratch files do not perturb the result.  Bytecode
counts are syntactic and are labelled as such: embedded data may disassemble as an opcode.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "Reasoning" / "RD_STEPPER_GAPS.md"
sys.path.insert(0, str(ROOT / "scripts"))

import audit_rd_sequences as seq  # noqa: E402
import check_rd_blocks_corpus as corpus  # noqa: E402
import generate_rd_blocks as generator  # noqa: E402


DECL = re.compile(
    r"(?m)^[ \t]*(?:(?:private|protected)\s+)?(?:theorem|lemma)\s+"
    r"(?P<name>(?:RD\.)?[A-Za-z_][A-Za-z0-9_']*)"
)
DECODE = re.compile(r"some\s*\(\s*\.([A-Z][A-Z0-9]*)\s*,\s*\.none\s*\)")


def tracked_lean_files(*roots: str) -> list[Path]:
    proc = subprocess.run(
        ["git", "ls-files", *roots], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
    )
    return [ROOT / p for p in sorted(proc.stdout.splitlines()) if p.endswith(".lean")]


def declaration_chunks(path: Path):
    clean = seq.strip_comments(path.read_text(encoding="utf-8"))
    matches = list(DECL.finditer(clean))
    for i, match in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(clean)
        line = clean.count("\n", 0, match.start()) + 1
        yield match.group("name"), line, clean[match.start():end]


def canonical_by_opcode() -> dict[str, set[str]]:
    found: dict[str, set[str]] = defaultdict(set)
    for rel in ("Reasoning/Reach.lean", "Reasoning/Solc.lean"):
        path = ROOT / rel
        for name, _line, chunk in declaration_chunks(path):
            if not name.startswith("RD."):
                continue
            for op in DECODE.findall(chunk):
                primitive = name.removeprefix("RD.").lower()
                accepted = {op.lower()}
                if op == "STATICCALL":
                    accepted.add("solcstaticcall")
                if op == "RETURN":
                    accepted.update({"ret", "rawret"})
                if op == "REVERT":
                    accepted.update({"rev", "rawrev"})
                if primitive in accepted:
                    found[op].add(name)
    return found


def local_workarounds():
    sites: dict[str, list[tuple[str, int, str]]] = defaultdict(list)
    for path in tracked_lean_files("Examples", "Benchmarks"):
        rel = path.relative_to(ROOT).as_posix()
        for name, line, chunk in declaration_chunks(path):
            if "Xstep" not in chunk or not re.search(r"\bstep_[A-Za-z0-9_]+", chunk):
                continue
            ops = list(dict.fromkeys(DECODE.findall(chunk)))
            for op in ops:
                sites[op].append((rel, line, name))
    return sites


def source_count(pattern: str, sources: list[str]) -> tuple[int, int]:
    regex = re.compile(pattern)
    hits = 0
    files = 0
    for clean in sources:
        n = len(regex.findall(clean))
        hits += n
        files += bool(n)
    return hits, files


def generator_gaps() -> dict[str, tuple[int, int]]:
    counts: Counter[str] = Counter()
    artifacts: dict[str, set[str]] = defaultdict(set)
    cases = corpus.discover([ROOT / "Examples", ROOT / "Benchmarks"])
    for case in cases:
        code = generator.strip_solidity_metadata(case.code)
        for ins in generator.disassemble(code):
            if not generator.instruction_is_supported(ins):
                label = ins.name.upper()
                counts[label] += 1
                artifacts[label].add(case.label)
    return {name: (count, len(artifacts[name])) for name, count in counts.items()}


def render() -> str:
    canonical = canonical_by_opcode()
    local = local_workarounds()
    gaps = generator_gaps()
    sources = [seq.strip_comments(path.read_text(encoding="utf-8"))
               for path in tracked_lean_files("Examples", "Benchmarks")]

    missing = [op for op in sorted(local) if op not in canonical]
    obsolete = [op for op in sorted(local) if op in canonical]

    call_rows = [
        ("`RD.call`", r"\bRD\.call\b"),
        ("`RD.callDepthLimit`", r"\bRD\.callDepthLimit\b"),
        ("`RD.solcStaticcall`", r"\bRD\.solcStaticcall\b"),
        ("`RD.solcStaticcallDepthLimit`", r"\bRD\.solcStaticcallDepthLimit\b"),
        ("`callCoincides`", r"\bcallCoincides\b"),
        ("`callNotMade_depthLimit`", r"\bcallNotMade_depthLimit\b"),
    ]

    out = [
        "# RD stepper and call-overhead audit",
        "",
        "Generated from tracked `Examples/**/*.lean` and `Benchmarks/**/*.lean` sources by "
        "`scripts/audit_rd_steppers.py`. Comments are stripped before counting.",
        "",
        "## Missing canonical RD steppers evidenced by local proofs",
        "",
        "These opcodes have a benchmark/example-local theorem that unfolds `Xstep` and invokes an "
        "EVM `step_*` lemma, but no opcode-matched `RD.*` theorem in `Reasoning/Reach.lean` or "
        "`Reasoning/Solc.lean`.",
        "",
        "| Opcode | Local workaround sites | Representative site |",
        "|---|---:|---|",
    ]
    for op in missing:
        rel, line, name = local[op][0]
        out.append(f"| `{op}` | {len(local[op])} | `{rel}:{line}` (`{name}`) |")
    if not missing:
        out.append("| _None_ | 0 | — |")

    out += [
        "",
        "## Local steppers now covered canonically",
        "",
        "These are deduplication opportunities rather than missing infrastructure.",
        "",
        "| Opcode | Local sites | Canonical theorem(s) |",
        "|---|---:|---|",
    ]
    for op in obsolete:
        out.append(f"| `{op}` | {len(local[op])} | " +
                   ", ".join(f"`{x}`" for x in sorted(canonical[op])) + " |")
    if not obsolete:
        out.append("| _None_ | 0 | — |")

    out += [
        "",
        "## Branch-specific call API footprint",
        "",
        "The counts below measure proof-script surface area, not kernel proof size or runtime. "
        "They show why a uniform outcome theorem is useful: made/depth APIs and their bridge "
        "lemmas recur together throughout the corpus.",
        "",
        "| API | References | Files |",
        "|---|---:|---:|",
    ]
    for label, pattern in call_rows:
        hits, files = source_count(pattern, sources)
        out.append(f"| {label} | {hits} | {files} |")

    out += [
        "",
        "## RD summary-generator boundaries",
        "",
        "The generator still splits at the following relevant opcodes. Counts are over a linear "
        "syntactic disassembly of discoverable byte arrays, after recognized Solidity metadata is "
        "removed; unreachable embedded data can therefore inflate them.",
        "",
        "| Opcode | Syntactic occurrences | Byte arrays | Status |",
        "|---|---:|---:|---|",
    ]
    for op in ("CALL", "STATICCALL"):
        count, artifacts = gaps.get(op, (0, 0))
        status = "RD semantics exist; generator cannot cross the boundary"
        out.append(f"| `{op}` | {count} | {artifacts} | {status} |")

    out += [
        "",
        "## Interpretation",
        "",
        "The concrete missing primitive steppers are the first table. CALL and STATICCALL are not "
        "missing semantic steppers; their problem is duplicated branch handling and a generator "
        "boundary. `RD.callOutcome`, `RD.callValueOutcome`, and `RD.staticcallOutcome` now package "
        "made and rejected attempts uniformly, while `TRD` records the actual completed attempt.",
        "",
    ]
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the committed report is stale")
    args = parser.parse_args(argv)
    report = render()
    if args.check:
        if not REPORT.exists() or REPORT.read_text(encoding="utf-8") != report:
            print(f"stale report: {REPORT.relative_to(ROOT)}", file=sys.stderr)
            return 1
        return 0
    print(report, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
