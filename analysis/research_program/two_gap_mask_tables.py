"""Local, proof-checked mark domains for the 0011 ordinary-exit chart.

SAT is used only to project a small physical rectangle. Block the listed
mask tuples and check the resulting UNSAT proof before using the table.
"""
from functools import lru_cache
from hashlib import sha256
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory
import gzip,json,subprocess
from .defect_window import table,window,DIR
from .odd_frames import frame

ROOT=Path('target/coupled_two_gap_catalogues')
VERIFIED=set()
@lru_cache(None)
def context(n,q):
    e=2+3*q;m=frame(n,(0,0,1,1));parent={(0,0):-1,(0,e):1};todo=list(parent)
    for i,j in todo:
        for d,(a,b) in enumerate(DIR):
            p=i+a,j+b
            if p not in parent and p in m and min(*p,n-1-p[0],n-1-p[1])==0 and (m[i,j] or m[p]):
                parent[p]=(d+2)%4;todo.append(p)
    assert len(parent)==4*n-4
    return m,parent
TABLE=lru_cache(None)(table)

def local(n,q,i,j,halo=4,drat=False,one=None):
    from pysat.solvers import Solver
    e=2+3*q
    if one is None:m,parent=context(n,q);star=(0,e);root=(0,0)
    else:
        from .slit_star_transfer import frame_path
        m,parent=frame_path(n,one);star=(2,e);root=(n-1,n-1)
    x,y=1+3*i,1+3*j
    dom=set(product(range(max(0,y-halo),min(n,y+6+halo)),range(max(0,x-halo),min(n,x+6+halo))))
    want=all(v in dom for v in (star,*[(star[0]+dy,star[1]+dx) for dy,dx in DIR
                                        if 0<=star[0]+dy<n and 0<=star[1]+dx<n]))
    def emit(f,bit,flags,arc,sheet):
        assert bool(flags)==want
        for p in sorted(dom):
            if p in m:f.append([bit(*p)*(1 if m[p] else -1)])
        # Ordinary north teeth other than the exit point toward their feet.
        if one is None:
            for h in range(max(3,x-halo),min(n-3,x+6+halo)):
                if h!=e and (1,h) in dom and (2,h) in dom:f.append([-bit(2,h),arc(2,h,3)])
        else:
            for u,v in sorted(dom):
                near=[(u+a,v+b) for a,b in DIR if 0<=u+a<n and 0<=v+b<n]
                if (u,v)==star:
                    for z in [(u,v),*near]:
                        if z in dom:f.append([-bit(*z)])
                elif all(z in dom for z in near):f.append([bit(u,v),*(bit(*z) for z in near)])
                if min(u,v,n-1-u,n-1-v)==2:
                    for d,(dy,dx) in enumerate(DIR):
                        foot=u+2*dy,v+2*dx
                        if (foot in m and m[foot] and min(*foot,n-1-foot[0],n-1-foot[1])==0
                            and (u+dy,v+dx) in dom):
                            f.append([-bit(u,v),arc(u,v,d)])
        vs=[bit(y+3*v+b,x+3*u+a) for u,v in product(range(2),repeat=2)
            for a,b in product(range(3),repeat=2)]
        ROOT.mkdir(exist_ok=True)
        with TemporaryDirectory(dir='target',prefix='certify_tile_') as tmp:
            cnf=Path(tmp)/'tile.cnf';drat=Path(tmp)/'tile.drat';f.to_file(str(cnf))
            sig=sha256(cnf.read_bytes()+str(vs).encode()).hexdigest()
            path=ROOT/(sig+'.json.gz');check=ROOT/(sig+'.check')
            if path.is_file() and check.is_file():
                raw=path.read_bytes();assert check.read_text().strip()=='VERIFIED '+sha256(raw).hexdigest()
                patterns=tuple(map(tuple,json.loads(gzip.decompress(raw))))
                if not drat or sig in VERIFIED:return patterns
                for w in patterns:
                    f.append([-z if w[j//9]>>(j%9)&1 else z for j,z in enumerate(vs)])
            else:
                patterns=[]
                with Solver(name='cadical195',bootstrap_with=f.clauses) as sol:
                    while sol.solve():
                        pos={v for v in sol.get_model() if v>0}
                        patterns.append(tuple(sum((z in pos)<<h for h,z in enumerate(vs[j:j+9])) for j in range(0,36,9)))
                        clause=[-z if z in pos else z for z in vs]
                        sol.add_clause(clause);f.append(clause)
            f.to_file(str(cnf))
            with open('/dev/null','wb') as dev:
                rc=subprocess.run(['target/cadical/build/cadical',str(cnf),str(drat)],stdout=dev).returncode
            assert rc==20
            log=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(drat)],capture_output=True,check=True).stdout
            assert b's VERIFIED' in log
            VERIFIED.add(sig)
            raw=gzip.compress(json.dumps(sorted(patterns),separators=(',',':')).encode(),mtime=0)
            path.write_bytes(raw);check.write_text('VERIFIED '+sha256(raw).hexdigest()+'\n')
            return tuple(sorted(patterns))
    return window(n,'rim',1,TABLE(n),domain=dom,defects={('s',*star)},want=want,exit_only=one is None,
                  matching=True,orient=parent,emit_graph=emit,root_site=root)
if __name__=='__main__':
    import sys
    p=local(*map(int,sys.argv[1:]));print('verified patterns',len(p))
