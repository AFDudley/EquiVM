#!/usr/bin/env python3
"""Compile the pinned closure with foundry.toml's Cancun/Vyper settings.

The shared scaffold compiler always disables Vyper metadata. Preserve its usual
artifacts, then restore the compiler-default creation trailer. Runtime code is
required to be identical. No shared generator or registry is changed.
"""
from pathlib import Path
import argparse
import json
import subprocess
import sys

directory = Path(__file__).resolve().parent
repo = directory.parents[1]
sys.path.insert(0, str(repo / "scripts"))
import scaffold

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--vyper", required=True)
args = parser.parse_args()
relative_dir = directory.relative_to(repo)
main = "curve_stablecoin/lending/Vault.vy"
status = scaffold.main(["compile", "--dir", str(relative_dir), "--vyper", args.vyper,
    "--main", main, "--contract", "Vault", "--evm-version", "cancun"])
if status:
    raise SystemExit(status)
source = directory / "contracts" / main
command = [args.vyper, "--evm-version", "cancun", "--path", str(directory / "contracts"),
           "-f", "combined_json", str(source)]
result = json.loads(subprocess.check_output(command, text=True))
artifact = result[str(source)]
runtime = artifact["bytecode_runtime"].removeprefix("0x")
creation = artifact["bytecode"].removeprefix("0x")
assert runtime == (directory / "runtime.hex").read_text().strip()
normalized = (directory / "creation.hex").read_text().strip()
assert creation.startswith(normalized)
assert len(creation) - len(normalized) == 130
(directory / "provenance" / "scaffold-no-metadata-creation.hex").write_text(normalized + "\n")
(directory / "provenance" / "foundry-default-creation.hex").write_text(creation + "\n")
(directory / "creation.hex").write_text(creation + "\n")
build_path = directory / "Vault.build.json"
build = json.loads(build_path.read_text())
build["settings"]["bytecodeMetadata"] = True
build["sourceMap"]["creation"] = artifact.get("source_map", {})
build_path.write_text(json.dumps(build) + "\n")
scaffold.write_hashes(directory, "Vault", directory / "contracts", ".vy")
print(f"restored compiler-default metadata: creation {len(creation)//2} bytes; runtime identical")
