"""Independently encode Erdos 895; no imported proof or encoding source.
Variables x_ij say ij is an edge. Clauses exclude triangles and independent
Schur triples with distinct positive vertices. This script is exploratory,
not a Lean proof or an independent UNSAT certificate checker.
"""
from itertools import combinations
from pathlib import Path
import argparse, json, os, subprocess, time
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--solver", default=os.environ.get("CADICAL", "cadical"), help="CaDiCaL executable")
parser.add_argument("--output", default="discovery", help="Output directory for a new discovery run")
args = parser.parse_args()
HERE = Path(args.output).resolve()
HERE.mkdir(parents=True, exist_ok=True)
SOLVER = args.solver
reports=[]
for n in (17,18):
    vertices=range(1,n+1)
    pairs=list(combinations(vertices,2))
    var={pair:i+1 for i,pair in enumerate(pairs)}
    clause_tri=[[-var[a,b],-var[a,c],-var[b,c]] for a,b,c in combinations(vertices,3)]
    triples=[(a,b,a+b) for a,b in pairs if a+b<=n]
    clause_schur=[[var[a,b],var[a,c],var[b,c]] for a,b,c in triples]
    clauses=clause_tri+clause_schur
    cnf=HERE/f'n{n}.cnf'
    cnf.write_text(f'p cnf {len(var)} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
    t=time.perf_counter()
    cmd=[SOLVER,'--no-binary',str(cnf),str(HERE/f'n{n}.drat')]
    result=subprocess.run(cmd, text=True,capture_output=True,timeout=90)
    elapsed=time.perf_counter()-t
    (HERE/f'n{n}.solver.log').write_text(result.stdout+result.stderr)
    row={'n':n,'variables':len(var),'triangle_clauses':len(clause_tri),'schur_clauses':len(triples),'total_clauses':len(clauses),'solver_exit':result.returncode,'seconds':elapsed}
    if result.returncode==10:
        signed=[int(s) for line in result.stdout.splitlines() if line.startswith('v ') for s in line[2:].split() if s!='0']
        positives={s for s in signed if s>0}
        edges={pair for pair,v in var.items() if v in positives}
        bad_tri=[(a,b,c) for a,b,c in combinations(vertices,3) if all(p in edges for p in ((a,b),(a,c),(b,c)))]
        bad_schur=[(a,b,c) for a,b,c in triples if all(p not in edges for p in ((a,b),(a,c),(b,c)))]
        assert not bad_tri and not bad_schur
        row.update(status='SAT',edge_count=len(edges),witness_checked=True,edges=sorted(edges))
    elif result.returncode==20:
        row.update(status='UNSAT',certificate_bytes=(HERE/f'n{n}.drat').stat().st_size,certificate_independently_checked=False)
    else: raise RuntimeError(result)
    reports.append(row)
    print(json.dumps(row))
(HERE/'results.json').write_text(json.dumps(reports,indent=2)+'\n')
