"""Simultaneous core placements for one residue of an arbitrarily far exit.

West, middle (exit-relative) and east clauses use common physical IDs
within each chart. No label equates marks merely separated by 42.
"""
from pathlib import Path
import json,subprocess,sys
from pysat.formula import IDPool
from .core413_seams import D,source,position
from .two_gap_board import Stream

def run(phase,seconds):
    tags,clauses=source();n=413;pool=IDPool();out=set()
    es=list(range(107,n-107,3));es=[e for e in es if e%42==phase];assert es
    # Row insertion is handled by the H=8 west/east strip transfer: all
    # y-band variables used in the raw core are marks or primal arrows at
    # depth <=5. All images of these sites are at the same fixed side.
    for e in es:
        def key(t,anchor):
            if t[0]=='row':return tuple(t)
            if t[0]=='s':return t[2]==e
            if t[0]=='frame' or t[0]=='axis':return True
            if t[0]=='col':return False
            assert t[0] in ('v','face','a','color')
            return (anchor,t[0],t[1],t[2]-(e if anchor=='C' else 0),*t[3:])
        ids={a:{z:(w if isinstance(w,bool) else pool.id(w)) for z,t in tags.items() if t[0]!='aux' for w in [key(t,a)]} for a in 'WCE'}
        for c in clauses:
            us=[tags[abs(z)] for z in c]
            if any(t[0]=='aux' for t in us):continue
            xs=[t[2] for t in us if len(t)>=3]
            # Mirrored far-side distance and stencil phase stay exact.
            # 's' may be chosen only in the middle; W/E images for this
            # representative stop at least three sites before the exit.
            for a in 'WCE':
                if xs and not {'W':max(xs)<e-3,'C':16<=min(xs) and max(xs)<=396,'E':min(xs)>e+3}[a]:continue
                ls=[]
                for z in c:
                    w=ids[a][abs(z)]
                    if isinstance(w,bool):
                        if w==(z>0):break
                    else:ls.append(w if z>0 else -w)
                else:out.add(tuple(sorted(ls)))
    stem=D/f'register_{phase}';p=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
    f=Stream(p);f.extend(sorted(out));f.to_file(str(p));print(phase,es,len(out),'clauses',flush=True)
    with stem.with_suffix('.log').open('wb') as fd:
        rc=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(p),str(pr)],stdout=fd).returncode
    if rc==20:
        chk=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],check=True,capture_output=True).stdout
        assert b's VERIFIED' in chk;stem.with_suffix('.check').write_bytes(chk);print(phase,'s VERIFIED',flush=True)
    elif rc==10:
        from pysat.solvers import Solver
        m={int(v) for l in stem.with_suffix('.log').open() if l.startswith('v ') for v in l.split()[1:]}
        assert not any(-v in m for v in m if v>0)
        with Solver(name='cadical195') as sol:
            for c in out:
                if not any(v in m for v in c):sol.add_clause([v for v in c if -v not in m])
            assert sol.solve();m.update(v for v in sol.get_model() if -v not in m)
        assert all(any(v in m for v in c) for c in out)
        print(phase,'checked SAT projection',flush=True)
    else:assert rc==0;print(phase,'UNKNOWN')
if __name__=='__main__':run(*map(int,sys.argv[1:]))
