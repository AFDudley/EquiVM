#!/usr/bin/env python3
"""Use the shared RD generator for this artifact's executable regions only.

The bytes and jump-destination tables remain complete. Dispatcher table bytes,
the creation payload and the compiler metadata are data, not additional code.
"""
from pathlib import Path
import re
import sys

directory = Path(__file__).resolve().parent
repo = directory.parents[1]
sys.path.insert(0, str(repo / "scripts"))
import generate_rd_blocks as rd

module = "Benchmarks.CurveVault"
runtime = bytes.fromhex((directory / "runtime.hex").read_text())
creation = bytes.fromhex((directory / "creation.hex").read_text())
assert len(runtime) == 8635 and runtime[8284:8288].hex() == "5b5f80fd"
assert creation[:17].hex() == "6121bb610011610000396121bb610000f3"
assert creation[17:8652] == runtime and len(creation) == 8717

for stem, prefix, code, limit, is_creation in [
    ("RuntimeBlocks", "vault", runtime, 8288, False),
    ("CreationBlocks", "vaultCreation", creation, 17, True),
]:
    code_term = f"{module}.{prefix}Bytecode"
    all_units = rd.generate_unit_records(code, prefix, code_term, creation_code=is_creation)
    def unit_pcs(unit):
        if unit.pcs:
            return unit.pcs
        # The shared generator leaves CALL/STATICCALL as explicit boundaries for
        # the body proof's external-call rule, rather than asserting a summary.
        return (int(re.search(r"boundary at pc (\d+):", unit.text)[1]),)
    units = [u for u in all_units if unit_pcs(u)[0] < limit]
    assert all(max(unit_pcs(u)) < limit for u in units)
    assert {pc for u in units for pc in unit_pcs(u)} == {
        instruction.pc for instruction in rd.disassemble(code) if instruction.pc < limit}
    paths = rd.write_outputs(directory / (stem + ".lean"), prefix,
        [module + ".Bytecode"], units, 20, is_creation, code_term,
        code=code if not is_creation else None)
    # These are this adapter's own generated shards. Remove surplus old shards
    # when the executable-only output replaces the initial whole-byte disassembly.
    for old in directory.glob(stem + "_*.lean"):
        if old not in paths:
            assert "Automatically generated RD summary" in old.read_text()
            old.unlink()
    print(f"{stem}: {len(units)} units, {len(paths)} shards; pcs 0..{limit-1}")
