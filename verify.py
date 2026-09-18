#!/usr/bin/env python3
"""Build all proof modules, audit ten exact axiom closures, and replay the kernel."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB_REV = "c5ea00351c28e24afc9f0f84379aa41082b1188f"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clean", action="store_true", help="Rebuild project modules; keep dependency caches")
    parser.add_argument("--output", default="verification/current", help="Directory for logs and receipt")
    args = parser.parse_args()
    logs = ROOT / args.output
    logs.mkdir(parents=True, exist_ok=True)
    receipt = logs / "receipt.json"
    receipt.write_text('{"status":"RUNNING"}\n')

    def sanitized(value):
        return value.replace(str(ROOT), "$PROJECT").replace(str(Path.home()), "$HOME")

    def run(name, command):
        print(name, flush=True)
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output = sanitized(result.stdout)
        (logs / (name + ".log")).write_text(output)
        if result.returncode:
            raise RuntimeError(f"{name} failed ({result.returncode}):\n{output}")
        return output

    try:
        config = json.loads((ROOT / "verification-targets.json").read_text())
        module = config["module"]
        expected = set(config["theorems"])
        if module != "Jsp746" or len(expected) != 10 or len(config["theorems"]) != 10:
            raise RuntimeError("Expected the exact ten-theorem Jsp746 verification configuration")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        mathlib = [p for p in manifest["packages"] if p["name"] == "mathlib"]
        if len(mathlib) != 1 or mathlib[0]["type"] != "git" or mathlib[0]["rev"] != MATHLIB_REV:
            raise RuntimeError("Unexpected Mathlib dependency pin")
        if any(p["type"] != "git" for p in manifest["packages"]):
            raise RuntimeError("Non-portable dependency in manifest")
        proofs = [ROOT / "Jsp746.lean", *sorted((ROOT / "Jsp746").rglob("*.lean"))]
        for path in proofs:
            if re.search(r"\b(?:sorry|admit|native_decide|axiom|unsafe)\b", path.read_text()):
                raise RuntimeError(f"Forbidden proof-source token in {path.relative_to(ROOT)}")
        if args.clean and (ROOT / ".lake/build").exists():
            shutil.rmtree(ROOT / ".lake/build")
        version = run("lean-version", ["lake", "env", "lean", "--version"])
        run("build", ["lake", "build", "--wfail"])
        audit = run("axioms", ["lake", "env", "lean", "Audit.lean"])
        if "warning:" in audit:
            raise RuntimeError("Warning in axiom audit")
        rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
        if len(rows) != 10 or {name for name, _ in rows} != expected:
            raise RuntimeError("Incomplete or unexpected axiom audit")
        axioms = {}
        for name, deps in rows:
            names = {s.strip() for s in deps.split(",") if s.strip()}
            if not names <= ALLOWED:
                raise RuntimeError(f"Unexpected axioms in {name}: {names - ALLOWED}")
            axioms[name] = sorted(names)
        run("kernel-replay", ["lake", "env", "leanchecker", "--fresh", "--verbose", module])
        run("python-data-check", [sys.executable, "scripts/check_data.py"])
        paths = proofs + [ROOT / name for name in (
            "Audit.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
            "verify.py", "verification-targets.json", "README.md", "NOTICE.md", "LICENSE", ".gitignore")]
        for folder in ("scripts", "data", ".github/workflows"):
            paths += [p for p in sorted((ROOT / folder).rglob("*"))
                      if p.is_file() and "__pycache__" not in p.parts and p.suffix != ".pyc"]
        hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
        commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True, capture_output=True)
        receipt.write_text(json.dumps({
            "status": "PASS", "checked_at_utc": datetime.now(timezone.utc).isoformat(),
            "lean_version": version.strip(), "scope": config["scope"],
            "clean_project_build": args.clean, "dependency_cache_reused": True,
            "github_actions": os.environ.get("GITHUB_ACTIONS") == "true",
            "checkout_commit": commit.stdout.strip() if commit.returncode == 0 else None,
            "mathlib_revision": MATHLIB_REV, "source_sha256": hashes, "axioms": axioms,
            "kernel_replay": "Official Lean kernel, fresh environment, all imported and local declarations; not a second independent implementation",
            "source_scan": "No sorry, admit, native_decide, custom axiom or unsafe declaration in proof sources",
            "python_checks": "Both CNF encodings, saved input hashes, and the 42-edge witness; corroborating evidence only",
        }, indent=2) + "\n")
        print("PASS: Jsp746, exactly 10 allowed axiom closures, fresh kernel replay, data checks", flush=True)
    except Exception as exc:
        error = sanitized(str(exc))
        receipt.write_text(json.dumps({"status": "FAIL", "error": error}, indent=2) + "\n")
        print(error, file=sys.stderr)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
