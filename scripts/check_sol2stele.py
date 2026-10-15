#!/usr/bin/env python3
"""Translate contracts with sol2stele.py (or vy2stele.py) and check that every draft elaborates.

Each directory must hold a ``<Name>.build.json`` (from ``scaffold.py compile``), a
``<Name>.sol.ast.json`` or a ``<Name>.vy.ast.json``; a Vyper build JSON or ``.vy.ast.json``
selects ``vy2stele.py``.  Drafts are written with holes as comments so the rest of the file is
checked; the summary lists the hole count and the first Lean error of each draft.

Example:
  scripts/check_sol2stele.py Benchmarks/Scaffolds/CometRewards Benchmarks/Scaffolds/Seaport/Conduit
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TRANSLATOR = ROOT / "scripts" / "sol2stele.py"
VYPER_TRANSLATOR = ROOT / "scripts" / "vy2stele.py"


def translator_for(directory: Path) -> Path:
    """``vy2stele.py`` for Vyper artifacts, ``sol2stele.py`` otherwise."""
    import json
    for build in sorted(directory.glob("*.build.json")):
        try:
            if json.loads(build.read_text(encoding="utf-8")).get("compiler", {}).get("kind") == "vyper":
                return VYPER_TRANSLATOR
        except (OSError, ValueError):
            continue
    if any(directory.glob("*.vy.ast.json")) and not any(directory.glob("*.sol.ast.json")):
        return VYPER_TRANSLATOR
    return TRANSLATOR


def lean_environment() -> tuple[str, dict[str, str]]:
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True,
                               capture_output=True, check=True).stdout.strip()
    toolchain = next(p for p in lean_path.split(":") if "toolchains" in p and p.endswith("lib/lean"))
    lean = str(Path(toolchain).parent.parent / "bin" / "lean")
    env = dict(os.environ)
    env["LEAN_PATH"] = lean_path
    return lean, env


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("directories", nargs="+", type=Path)
    parser.add_argument("--keep", type=Path, help="keep the drafts in this directory")
    parser.add_argument("--contract", action="append", default=[],
                        help="DIR=Name to pick a contract where the build json is ambiguous")
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args(argv)
    names = dict(item.split("=", 1) for item in args.contract)
    lean, env = lean_environment()
    failures = 0
    with tempfile.TemporaryDirectory(prefix="equivm-sol2stele-") as tmp:
        root = Path(tmp)
        (root / "Drafts").mkdir()
        for directory in args.directories:
            label = directory.name
            draft = root / "Drafts" / f"{re.sub(r'[^A-Za-z0-9]', '_', label)}.lean"
            command = [sys.executable, str(translator_for(directory)), str(directory), "--namespace", f"Drafts.{label}",
                       "--comment-holes", "--output", str(draft)]
            if str(directory) in names:
                command += ["--contract", names[str(directory)]]
            translated = subprocess.run(command, text=True, capture_output=True, check=False)
            if translated.returncode != 0:
                failures += 1
                print(f"FAIL {label}: translator: {(translated.stderr or translated.stdout).strip().splitlines()[-1]}")
                continue
            holes = translated.stdout.strip()
            try:
                checked = subprocess.run([lean, str(draft.relative_to(root))], cwd=root, env=env, text=True,
                                         capture_output=True, check=False, timeout=args.timeout)
                error = next((line for line in (checked.stdout + checked.stderr).splitlines()
                              if ": error:" in line), None)
                ok = checked.returncode == 0 and error is None
            except subprocess.TimeoutExpired:
                ok, error = False, f"lean timed out after {args.timeout}s"
            if args.keep:
                args.keep.mkdir(parents=True, exist_ok=True)
                (args.keep / draft.name).write_text(draft.read_text(encoding="utf-8"), encoding="utf-8")
            status = "ok  " if ok else "FAIL"
            failures += 0 if ok else 1
            detail = holes.split(": ", 1)[-1] if ": " in holes else holes
            print(f"{status} {label}: {detail}" + ("" if ok else f" — {error}"))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
