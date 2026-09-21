#!/usr/bin/env python3
"""Build the complete proof, audit its axioms, and replay a fresh Lean kernel."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB_REVISION = "c5ea00351c28e24afc9f0f84379aa41082b1188f"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clean", action="store_true", help="Remove project build outputs; retain dependency caches")
    parser.add_argument("--output", default="verification/current", help="Directory for logs and the source-hash receipt")
    args = parser.parse_args()
    config = json.loads((ROOT / "verification-targets.json").read_text())
    module = config["module"]
    expected = set(config["theorems"])
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
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        packages = manifest["packages"]
        if any(p["type"] != "git" for p in packages):
            raise RuntimeError("The public manifest must contain Git dependencies only")
        if next(p["rev"] for p in packages if p["name"] == "mathlib") != MATHLIB_REVISION:
            raise RuntimeError("Unexpected Mathlib revision")
        proofs = [ROOT / (module + ".lean"), *sorted((ROOT / module).rglob("*.lean"))]
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
        if len(rows) != len(expected) or {name for name, _ in rows} != expected:
            raise RuntimeError("Incomplete or unexpected axiom audit")
        axioms = {}
        for name, deps in rows:
            names = {s.strip() for s in deps.split(",") if s.strip()}
            if not names <= ALLOWED:
                raise RuntimeError(f"Unexpected axioms in {name}: {sorted(names - ALLOWED)}")
            axioms[name] = sorted(names)
        run("kernel-replay", ["lake", "env", "leanchecker", "--fresh", "--verbose", module])

        dependency_commits = {}
        for package in packages:
            checkout = ROOT / ".lake/packages" / package["name"]
            actual = subprocess.run(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                                    text=True, capture_output=True, check=True).stdout.strip()
            if actual != package["rev"]:
                raise RuntimeError(f"Dependency revision mismatch: {package['name']}")
            dirty = subprocess.run(["git", "-C", str(checkout), "status", "--porcelain", "--untracked-files=no"],
                                   text=True, capture_output=True, check=True).stdout
            if dirty:
                raise RuntimeError(f"Tracked dependency changes: {package['name']}")
            dependency_commits[package["name"]] = actual

        paths = proofs + [ROOT / name for name in (
            "Audit.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
            "verify.py", "verification-targets.json", "README.md", "NOTICE.md", "LICENSE", ".gitignore")]
        paths += sorted((ROOT / ".github/workflows").glob("*.yml"))
        hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
        commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True, capture_output=True)
        status = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no"],
                                cwd=ROOT, text=True, capture_output=True)
        receipt.write_text(json.dumps({
            "status": "PASS", "checked_at_utc": datetime.now(timezone.utc).isoformat(),
            "lean_version": version.strip(), "scope": config["scope"],
            "clean_project_build": args.clean,
            "dependency_cache_reused": True,
            "github_actions": os.environ.get("GITHUB_ACTIONS") == "true",
            "checkout_commit": commit.stdout.strip() if commit.returncode == 0 else None,
            "tracked_worktree_dirty": bool(status.stdout.strip()) if status.returncode == 0 else None,
            "mathlib_revision": MATHLIB_REVISION,
            "dependency_commits": dependency_commits,
            "source_sha256": hashes, "axioms": axioms,
            "kernel_replay": "Official Lean kernel, fresh environment, all imported and local declarations; not a second independent implementation",
            "source_scan": "No sorry, admit, native_decide, custom axiom or unsafe declaration in proof sources",
        }, indent=2) + "\n")
        print(f"PASS: {module}, {len(expected)} axiom closures, fresh kernel replay", flush=True)
    except Exception as exc:
        receipt.write_text(json.dumps({"status": "FAIL", "error": sanitized(str(exc))}, indent=2) + "\n")
        raise


if __name__ == "__main__":
    main()
