"""Boundary fluxes of the exceptional-tail tile system (over GF(2))."""
from itertools import product
from pathlib import Path
import sys,subprocess
from .defect_window import window,table

def enumerate_blocks(axis=0,cert=False):
    from pysat.solvers import Solver
    x=40;blocks=[]
    def emit(f,bit,flags):
        vs=[[bit(x+a+3*i,x+b+3*j) for a,b in product(range(3),repeat=2)] for i,j in product(range(2),repeat=2)]
        if axis:
            for t in vs:
                for k in ((3,5) if axis==1 else (1,7)):f.append([-t[4],-t[k]])
        with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
            while s.solve():
                m=set(s.get_model());blocks.append(tuple(sum((z in m)<<k for k,z in enumerate(t)) for t in vs))
                c=[-z if z in m else z for t in vs for z in t];s.add_clause(c);f.append(c)
        if cert:
            stem=Path(f'target/tile_flux_{axis}');fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat');f.to_file(str(fn))
            with stem.with_suffix('.log').open('wb') as log:assert subprocess.run(['target/cadical/build/cadical',str(fn),str(pr)],stdout=log).returncode==20
            proof=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True,check=True).stdout
            assert b's VERIFIED' in proof;stem.with_suffix('.check').write_bytes(proof)
            print('2x2 projection s VERIFIED',flush=True)
    window(119,'rim',1,table(119),want=False,domain=set(product(range(34,52),repeat=2)),emit=emit,turn_domain=set())
    return sorted(blocks)

def edges(b):
    a,c,d,e=b
    return ((0,a,c),(1,c,e),(0,d,e),(1,a,d))

def basis(blocks):
    es=sorted({e for b in blocks for e in edges(b)});idx={e:k for k,e in enumerate(es)};piv={}
    def insert(v):
        while v:
            i=v.bit_length()-1
            if i not in piv:piv[i]=v;return
            v^=piv[i]
    def vec(b):
        v=0
        for e in edges(b):v^=1<<idx[e]
        return v
    for b in blocks:insert(vec(b))
    # Fix one edge on a spanning tree of the tile-mask graph: the
    # corresponding gradients sum to zero on every closed word anyway.
    parent={}
    def root(u):
        while u in parent:u=parent[u]
        return u
    for k,(d,u,v) in enumerate(es):
        a,b=root(u),root(v)
        if a!=b:parent[a]=b;insert(1<<k)
    # Mod out the two translation constants, by fixing a horizontal and
    # a vertical loop at any realizable constant phase.
    for d in (0,1):
        k=next(k for k,(dd,u,v) in enumerate(es) if d==dd and u==v);insert(1<<k)
    sol=[]
    for k in range(len(es)):
        if k in piv:continue
        v=1<<k
        for i,r in sorted(piv.items()):
            if (v&r).bit_count()%2:v|=1<<i
        assert all(not (vec(b)&v).bit_count()%2 for b in blocks)
        sol.append(v)
    print('plaquettes',len(blocks),'edge words',len(es),'nontrivial GF(2) boundary fluxes',len(sol),
          'basis supports',sorted(v.bit_count() for v in sol),flush=True)
    return es,sol

if __name__=='__main__':basis(enumerate_blocks(int(sys.argv[1]),'--cert' in sys.argv))
