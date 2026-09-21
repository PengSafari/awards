#!/usr/bin/env python3
"""Independently check Li's JSP-000690 witness using Python's standard library.

This is an exhaustive computational reproduction, not a Lean proof or new result.
Run: python3 verify.py [witness.json]
"""
import hashlib
import itertools
import json
from pathlib import Path
import sys


def check(witness):
    vertices = witness["vertices"]
    edges = [frozenset(edge) for edge in witness["edges"]]
    vertex_set = set(vertices)
    assert len(vertices) == len(vertex_set) == 9
    assert len(edges) == len(set(edges)) == 22
    assert all(len(edge) == 3 and edge <= vertex_set for edge in edges)

    def proper(es, coloring):
        return all(len({coloring[v] for v in edge}) >= 2 for edge in es)

    degrees = [sum(v in edge for edge in edges) for v in vertices]
    assert degrees == [10, 7, 7, 7, 7, 7, 7, 7, 7]

    # Recompute all binary colorings; no solver trace or stored result is trusted.
    colorings = [dict(zip(vertices, bits))
                 for bits in itertools.product((0, 1), repeat=len(vertices))]
    proper_count = sum(proper(edges, coloring) for coloring in colorings)
    assert proper_count == 0

    three = {int(v): c for v, c in witness["three_coloring"].items()}
    assert set(three) == vertex_set and set(three.values()) <= {0, 1, 2}
    assert proper(edges, three)

    edge_certs = witness["edge_deletion_certificates"]
    assert len(edge_certs) == len(edges)
    assert {frozenset(c["deleted_edge"]) for c in edge_certs} == set(edges)
    for cert in edge_certs:
        deleted = frozenset(cert["deleted_edge"])
        blue = set(cert["blue_vertices"])
        assert blue <= vertex_set
        coloring = {v: int(v in blue) for v in vertices}
        assert proper([edge for edge in edges if edge != deleted], coloring)
        assert not proper([deleted], coloring)

    vertex_certs = witness["vertex_deletion_certificates"]
    assert len(vertex_certs) == len(vertices)
    assert {c["deleted_vertex"] for c in vertex_certs} == vertex_set
    for cert in vertex_certs:
        deleted = cert["deleted_vertex"]
        blue = set(cert["blue_vertices"])
        assert blue <= vertex_set - {deleted}
        coloring = {v: int(v in blue) for v in vertices if v != deleted}
        assert proper([edge for edge in edges if deleted not in edge], coloring)

    return {
        "status": "PASS",
        "vertices": len(vertices), "edges": len(edges),
        "degrees": degrees, "minimum_degree": min(degrees),
        "binary_colorings_checked": len(colorings),
        "proper_binary_colorings": proper_count,
        "proper_three_coloring": True,
        "edge_deletion_certificates_checked": len(edge_certs),
        "vertex_deletion_certificates_checked": len(vertex_certs),
        "scope": "Python reproduction of an existing construction; not Lean verified",
    }


def main():
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent / "data" / "witness.json"
    raw = path.read_bytes()
    result = check(json.loads(raw))
    result["witness_sha256"] = hashlib.sha256(raw).hexdigest()
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
