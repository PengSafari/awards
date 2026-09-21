#!/usr/bin/env python3
"""Corroborate both CNF encodings and the 17-point witness, without a SAT solver."""
from itertools import combinations
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"

for n in (17, 18):
    pairs = list(combinations(range(1, n + 1), 2))
    variables = {edge: index + 1 for index, edge in enumerate(pairs)}
    triangles = [[-variables[a, b], -variables[a, c], -variables[b, c]]
                 for a, b, c in combinations(range(1, n + 1), 3)]
    sums = [[variables[a, b], variables[a, a + b], variables[b, a + b]]
            for a, b in pairs if a + b <= n]
    clauses = triangles + sums
    encoded = f"p cnf {len(pairs)} {len(clauses)}\n" + "".join(
        " ".join(map(str, clause)) + " 0\n" for clause in clauses)
    if (DATA / f"n{n}.cnf").read_text() != encoded:
        raise SystemExit(f"n{n}.cnf differs from the mathematical encoding")

witness = json.loads((DATA / "witness.json").read_text())
edges = [tuple(edge) for edge in witness["edges"]]
if witness["n"] != 17 or len(edges) != 42 or len(set(edges)) != 42:
    raise SystemExit("Wrong witness order or edge count")
if not all(1 <= a < b <= 17 for a, b in edges):
    raise SystemExit("Invalid witness label")
edge_set = set(edges)
for a, b, c in combinations(range(1, 18), 3):
    if all(e in edge_set for e in ((a, b), (a, c), (b, c))):
        raise SystemExit(f"Triangle: {a, b, c}")
for a, b in combinations(range(1, 18), 2):
    if a + b <= 17 and all(e not in edge_set for e in ((a, b), (a, a + b), (b, a + b))):
        raise SystemExit(f"Independent Schur triple: {a, b, a + b}")
source = (ROOT / "Jsp746/Witness.lean").read_text().split("def witnessEdges", 1)[1].split("def witnessAdj", 1)[0]
lean_edges = [(int(a), int(b)) for a, b in re.findall(r"\((\d+),\s*(\d+)\)", source)]
if lean_edges != edges:
    raise SystemExit("Lean witness and packaged witness differ")
metadata = json.loads((ROOT / "scripts/refutation-generation.json").read_text())
for name, key in (("n18.cnf", "cnf_sha256"), ("n18.drat", "trace_sha256")):
    if hashlib.sha256((DATA / name).read_bytes()).hexdigest() != metadata[key]:
        raise SystemExit(f"Saved generator input hash mismatch: {name}")
print("PASS: both exact CNF encodings, saved input hashes, and the triangle-free 42-edge Schur obstruction")
