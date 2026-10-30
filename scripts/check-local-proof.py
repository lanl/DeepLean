#!/usr/bin/env python3
"""Build and replay DeepLean proofs locally; this is not confined certification."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
THEOREMS = ["DeepLean.Attention." + name for name in (
    "normalizer_counterexample", "softmax_identifiability", "softmax_generic_identifiability")]
AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def source_hashes():
    paths = sorted((ROOT / "DeepLean").rglob("*.lean")) + [ROOT / name for name in (
        "DeepLean.lean", "Challenge.lean", "Solution.lean", "lean-toolchain",
        "lakefile.toml", "lake-manifest.json", "comparator.json", "formalization.yaml",
        "scripts/check-local-proof.py", "scripts/check-attention-interface.py",
        "scripts/validate-formalization.rb")]
    return {str(path.relative_to(ROOT)): sha256(path) for path in paths}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-dir", type=Path, help="new output directory; existing paths are refused")
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = (args.evidence_dir or ROOT / ".cache/local-proof" / stamp).resolve()
    evidence.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    env["UV_CACHE_DIR"] = str(ROOT / ".cache/uv")
    env["ELAN_TOOLCHAIN"] = (ROOT / "lean-toolchain").read_text().strip()
    record = {"kind": "local-development-checks", "status": "running",
              "confined": False, "registry_submission": False, "started_utc": stamp,
              "host": {"system": platform.system(), "machine": platform.machine(),
                       "release": platform.release()},
              "theorems": THEOREMS, "permitted_axioms": sorted(AXIOMS),
              "source_sha256": source_hashes(), "steps": []}

    def save():
        (evidence / "report.json").write_text(json.dumps(record, indent=2) + "\n")

    def run(name, argv, input_text=None, output=None):
        print(f"{name}: {evidence / (name + '.log')}", flush=True)
        step = {"name": name, "argv": [str(x) for x in argv]}
        record["steps"].append(step)
        save()
        with (evidence / (name + ".log")).open("wb") as log:
            if output:
                with output.open("wb") as target:
                    result = subprocess.run(argv, cwd=ROOT, env=env, stdout=target, stderr=log)
            else:
                result = subprocess.run(argv, cwd=ROOT, env=env,
                                        input=input_text.encode() if input_text else None,
                                        stdout=log, stderr=subprocess.STDOUT)
        step["exit_code"] = result.returncode
        save()
        if result.returncode:
            raise RuntimeError(f"{name} failed with exit {result.returncode}; inspect its log")
        return (evidence / (name + ".log")).read_text()

    try:
        config = json.loads((ROOT / "comparator.json").read_text())
        if (config["theorem_names"] != THEOREMS or config["definition_names"] != []
                or set(config["permitted_axioms"]) != AXIOMS or config["enable_nanoda"] is not True
                or config["challenge_module"] != "Challenge" or config["solution_module"] != "Solution"):
            raise ValueError("unexpected proof interface or axiom/checker policy")
        python = subprocess.check_output(["uv", "python", "find", "3.14.5"], cwd=ROOT, env=env, text=True).strip()
        env["PYTHON3"] = python
        lean = Path(subprocess.check_output(["elan", "which", "lean"], cwd=ROOT, env=env, text=True).strip())
        bindir = lean.parent
        env["PATH"] = str(bindir) + os.pathsep + env.get("PATH", "")
        tools = ["lean", "lake", "leanexport", "leanchecker", "nanoda_bin", "con-ron"]
        record["toolchain"] = env["ELAN_TOOLCHAIN"]
        record["tool_sha256"] = {name: sha256(bindir / name) for name in tools}
        record["checker_sha256"] = sha256(Path(__file__))
        record["lean_version"] = run("lean-version", [str(lean), "--version"]).strip()
        record["python_version"] = run("python-version", [python, "--version"]).strip()
        run("interface", [python, "scripts/check-attention-interface.py"])
        run("metadata", ["ruby", "scripts/validate-formalization.rb"])
        # Only this package's outputs are discarded; downloaded dependencies remain cached.
        run("clean", [str(bindir / "lake"), "clean", "DeepLean"])
        run("build", [str(bindir / "lake"), "build"])
        for module in ("Challenge", "Solution"):
            run(module.lower(), [str(bindir / "lake"), "env", "lean", module + ".lean"])
        completed = sorted((ROOT / "DeepLean").rglob("*.lean")) + [ROOT / "DeepLean.lean", ROOT / "Solution.lean"]
        for path in completed:
            if re.search(r"\b(sorry|admit|axiom|unsafe)\b", path.read_text()):
                raise ValueError(f"review required for forbidden source token in {path.relative_to(ROOT)}")
        audit = "import Solution\n" + "".join("#print axioms " + name + "\n" for name in THEOREMS)
        axioms = run("axioms", [str(bindir / "lake"), "env", "lean", "--stdin", "--trust=0"], audit)
        parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", axioms)
        if {name for name, _ in parsed} != set(THEOREMS):
            raise ValueError("axiom audit did not report every selected theorem")
        for name, values in parsed:
            if set(values.replace("\n", " ").replace(" ", "").split(",")) != AXIOMS:
                raise ValueError(f"unexpected transitive axioms for {name}")
        # Export the same primitive and quotient targets that this pinned Lake compares.
        check_source = (bindir.parent / "src/lean/lake/Lake/CLI/Check.lean").read_text()
        primitive_block = check_source.split("def primitiveTargets", 1)[1].split("def builtinTargets", 1)[0]
        primitive_block = re.sub(r"--[^\n]*", "", primitive_block)
        primitives = re.findall(r"``([A-Za-z0-9_.]+)", primitive_block)
        if not primitives:
            raise ValueError("cannot identify pinned Comparator primitive targets")
        targets = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] + THEOREMS + sorted(AXIOMS) + primitives
        for module in ("Challenge", "Solution"):
            run("export-" + module.lower(), [str(bindir / "lake"), "env", str(bindir / "leanexport"),
                                              module, "--", *targets], output=evidence / (module.lower() + ".ndjson"))
        comparator = run("comparator", [str(bindir / "lake"), "comparator", "--config", "comparator.json",
                         "--challenge-from-export", str(evidence / "challenge.ndjson"),
                         "--solution-from-export", str(evidence / "solution.ndjson"), "--inadvisably-no-sandbox"])
        for marker in ("Your solution is okay!", "nanoda kernel accepts the solution", "Lean default kernel accepts the solution"):
            if marker not in comparator:
                raise ValueError(f"Comparator report lacks {marker!r}")
        run("con-ron", [str(bindir / "con-ron"), "--jobs=2", str(evidence / "solution.ndjson")])
        if source_hashes() != record["source_sha256"]:
            raise ValueError("proof sources or configuration changed during the checks")
        record["export_sha256"] = {name: sha256(evidence / name) for name in ("challenge.ndjson", "solution.ndjson")}
        record["status"] = "pass"
    except (OSError, ValueError, RuntimeError, KeyError, IndexError,
            subprocess.CalledProcessError, KeyboardInterrupt) as error:
        record["status"] = "fail"
        record["error"] = str(error) or type(error).__name__
        print(f"FAIL: {error}", file=sys.stderr)
    finally:
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
    print(f"{record['status'].upper()}: {evidence / 'report.json'}")
    return 0 if record["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
