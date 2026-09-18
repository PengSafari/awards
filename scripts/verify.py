#!/usr/bin/env python3
"""Build the full proof, audit its axioms, replay the kernel, and check the witness."""
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

ROOT = Path(__file__).resolve().parent.parent
EXPECTED = {
    "Jsp690.jsp_000690", "Jsp690.jsp_000690_nine_vertices",
    "Jsp690.witness_actual_vertex_critical", "Jsp690.witness_not_two_colorable",
    "Jsp690.witness_edge_deletion_certificates", "Jsp690.colorable_of_proper",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clean", action="store_true", help="Remove this project's build output first; keep dependency caches")
    parser.add_argument("--output", default="verification/current", help="Log and receipt directory")
    args = parser.parse_args()
    logs = ROOT / args.output
    logs.mkdir(parents=True, exist_ok=True)
    receipt = logs / "receipt.json"
    receipt.write_text(json.dumps({"status": "running"}, indent=2) + "\n")

    def sanitized(value):
        value = value.replace(str(ROOT), "$PROJECT")
        return value.replace(str(Path.home()), "$HOME")

    def run(name, command):
        print(name, flush=True)
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output = sanitized(result.stdout)
        (logs / (name + ".log")).write_text(output)
        if result.returncode:
            receipt.write_text(json.dumps({"status": "FAIL", "step": name, "exit_code": result.returncode}, indent=2) + "\n")
            print(output, file=sys.stderr)
            raise SystemExit(result.returncode)
        return output

    if args.clean and (ROOT / ".lake/build").exists():
        shutil.rmtree(ROOT / ".lake/build")
    version = run("lean-version", ["lake", "env", "lean", "--version"])
    run("build", ["lake", "build"])
    audit = run("axioms", ["lake", "env", "lean", "Audit.lean"])
    audited = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
    if len(audited) != len(EXPECTED) or {name for name, _ in audited} != EXPECTED:
        raise SystemExit("Incomplete or unexpected axiom audit output")
    axioms = {}
    for name, deps in audited:
        names = {s.strip() for s in deps.split(",") if s.strip()}
        if not names <= ALLOWED:
            raise SystemExit("Unexpected axioms for " + name + ": " + repr(names - ALLOWED))
        axioms[name] = sorted(names)
    run("kernel-replay", ["lake", "env", "leanchecker", "--fresh", "--verbose", "Jsp690"])
    run("python-cross-check", [sys.executable, "scripts/check_witness.py"])

    source_paths = ["Jsp690.lean", "Audit.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json", "data/witness.json"]
    for folder, suffix in [("Jsp690", "*.lean"), ("scripts", "*.py"), (".github/workflows", "*.yml")]:
        source_paths.extend(str(p.relative_to(ROOT)) for p in sorted((ROOT / folder).glob(suffix)))
    hashes = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in source_paths}
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True, capture_output=True)
    receipt.write_text(json.dumps({
        "status": "PASS", "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version.strip(), "clean_project_build": args.clean,
        "github_actions": os.environ.get("GITHUB_ACTIONS") == "true",
        "checkout_commit": commit.stdout.strip() if commit.returncode == 0 else None,
        "source_sha256": hashes, "axioms": axioms,
        "kernel_replay": "Official Lean kernel in fresh mode, including imported constants; not an independent implementation",
        "scope": "Full chromatic JSP-000690, formalizing Ruiliang Li's known construction",
    }, indent=2) + "\n")
    print("PASS: complete theorem, allowed axioms only, fresh kernel replay, Python cross-check", flush=True)


if __name__ == "__main__":
    main()
