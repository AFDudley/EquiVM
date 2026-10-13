#!/usr/bin/env python3
"""Run the repository differential CLI with only the local Vault target registered."""
from pathlib import Path
import json
import os
import subprocess
import sys

directory = Path(__file__).resolve().parent
repo = directory.parents[1]
runner = directory / ".difftest"
runner.mkdir(exist_ok=True)
(runner / "lakefile.toml").write_text(
    'name = "CurveVaultDiff"\nversion = "0.1.0"\n'
    'packagesDir = ' + json.dumps(str(repo / ".lake/packages")) + '\n'
    '[[require]]\nname = "EquiVM"\npath = ' + json.dumps(str(repo)) + '\n'
    '[[lean_exe]]\nname = "solm-difftest"\nroot = "Main"\n')
(runner / "lean-toolchain").write_text((repo / "lean-toolchain").read_text())
main = (repo / "Tests/DiffTest/Main.lean").read_text()
main = main.replace("import Tests.DiffTest.Targets", "import Benchmarks.CurveVault.DiffTarget")
main = main.replace("open Solm.DiffTest Tests.DiffTest",
                    "open Solm.DiffTest\n\ndef allTargets : List Target :=\n"
                    "  [Benchmarks.CurveVault.diffTarget]")
(runner / "Main.lean").write_text(main)
manifest = json.loads((repo / "lake-manifest.json").read_text())
manifest["name"] = "CurveVaultDiff"
manifest["packagesDir"] = str(repo / ".lake/packages")
manifest["packages"].append(dict(type="path", name="EquiVM", dir=str(repo),
    manifestFile="lake-manifest.json", configFile="lakefile.toml", inherited=False))
(runner / "lake-manifest.json").write_text(json.dumps(manifest))
corpus = runner / "EthereumTests"
if not corpus.exists():
    corpus.symlink_to(repo / ".lake/packages/evmlean/EthereumTests", target_is_directory=True)
ethereum = runner / "Ethereum"
if not ethereum.exists():
    ethereum.symlink_to(repo / ".lake/packages/evmlean/Ethereum", target_is_directory=True)
env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
venv_bin = runner / ".venv" / "bin"
if (venv_bin / "python3").exists():
    env["PATH"] = str(venv_bin) + os.pathsep + env.get("PATH", "")
subprocess.run(["python3", "-c", "import Crypto.Hash.RIPEMD160, eth_typing.bls, py_ecc.bls"],
               env=env, check=True)
raise SystemExit(subprocess.call(["lake", "exe", "solm-difftest", *sys.argv[1:]], cwd=runner, env=env))
