"""Small independent reverse-unit-propagation checker for this probe's trace.
Deletion steps remove one matching live clause. Every addition must follow
by unit propagation after negating its literals. No RAT fallback is used.
This is a Python checker, not a formally verified checker.
"""
from pathlib import Path
from collections import Counter
import json,time
HERE=Path(__file__).resolve().parents[1] / "data"

def parse(line):
    c=tuple(sorted(map(int,line.split()[:-1])))
    assert 0 not in c
    return c

def rup(clauses,clause):
    values={}
    for literal in clause:
        var=abs(literal); val=literal<0
        if var in values and values[var]!=val: return True
        values[var]=val
    while True:
        progress=False
        for row in clauses:
            open_lit=None
            count=0
            for lit in row:
                var=abs(lit)
                if var in values:
                    if values[var]==(lit>0): break
                else:
                    count+=1
                    open_lit=lit
            else:
                if count==0:return True
                if count==1:
                    values[abs(open_lit)]=open_lit>0
                    progress=True
                continue
        if not progress:return False

live=Counter(parse(s) for s in (HERE/'n18.cnf').read_text().splitlines() if s and s[0] not in 'cp')
t=time.perf_counter(); additions=deletions=0; empty=False
for number,line in enumerate((HERE/'n18.drat').read_text().splitlines(),1):
    if line.startswith('d '):
        clause=parse(line[2:])
        assert live[clause]>0,(number,'missing deletion',clause)
        live[clause]-=1
        if not live[clause]:del live[clause]
        deletions+=1
    else:
        clause=parse(line)
        assert rup(live,clause),(number,'not RUP',clause)
        live[clause]+=1
        additions+=1
        empty=empty or not clause
assert empty,'No empty clause'
report={'verified':True,'checker':'own Python reverse-unit-propagation checker','formal_lean_proof':False,'additions':additions,'deletions':deletions,'seconds':time.perf_counter()-t}
print(json.dumps(report))
