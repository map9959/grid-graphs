"""Eliminate deep plaquettes by propagating two-tile words to three clean sides."""
from itertools import product
from pathlib import Path
from collections import defaultdict
import subprocess,sys
from .defect_window import table,window
from .tile_circulation import enumerate_blocks,edges

def ports(T,d,far,cert):
    from .saturated_tile_phase import relation
    n=119;h=6;along=range(40-h,46+h);normal=range(n-16-h,n) if far else range(16+h)
    dom=set(product(normal,along) if not d else product(along,normal))
    result=[]
    def emit(f,bit,flags):
        for i,j in sorted(dom):
            dist=min(i,j,n-1-i,n-1-j)
            if dist<2:f.append([bit(i,j)*(1 if dist==0 else -1)])
        tiles=[[bit(*(((n-16 if far else 13)+a,40+3*k+b) if not d else
                       (40+3*k+a,(n-16 if far else 13)+b))) for a,b in product(range(3),repeat=2)] for k in (0,1)]
        g=relation(f,tiles);result.extend((a,b) for a,bs in g.items() for b in bs)
        if cert:
            stem=Path(f'target/tile_flux_ports_{d}_{far}');fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
            f.to_file(str(fn))
            with stem.with_suffix('.log').open('wb') as fd:assert subprocess.run(['target/cadical/build/cadical',str(fn),str(pr)],stdout=fd).returncode==20
            proof=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True,check=True).stdout
            assert b's VERIFIED' in proof;stem.with_suffix('.check').write_bytes(proof)
    window(n,'rim',1,T,want=False,domain=dom,matching=True,emit=emit)
    return set(result)

def closure(initial,pp,free):
    blocks=set(initial)
    while True:
        accept={}
        for d in (0,1):
            graph=defaultdict(set);back=defaultdict(set)
            for block in blocks:
                e=edges(block)
                u,v=(e[0][1:],e[2][1:]) if d==0 else (e[3][1:],e[1][1:])
                graph[u].add(v);back[v].add(u)
            nodes=set(graph)|set(back);ok=nodes.copy()
            for far,g in ((0,graph),(1,back)):
                if (d,far)==free:continue
                s=pp[d,far]&nodes
                while (q:=s.union(*(g.get(x,()) for x in s)))!=s:s=q
                ok.intersection_update(s)
            accept[d]=ok
        new={b for b in blocks if all(e[1:] in accept[e[0]] for e in edges(b))}
        if new==blocks:return sorted(new)
        blocks=new

def run(cert):
    T=table(119);ps={(d,f):ports(T,d,f,cert) for d,f in product(range(2),repeat=2)}
    bs=enumerate_blocks(0,cert);print('clean edge ports',[(k,len(v)) for k,v in ps.items()])
    for ax in (0,1,2):
        orig=[b for b in bs if not ax or all(not(m&16 and m&(40 if ax==1 else 130)) for m in b)]
        for free in ((0,0),None):
            alive=closure(orig,ps,free)
            if not alive:print('EMPTY');continue
            alphabet=set(m for b in alive for m in b)
            print('axis',ax,'unconstrained side',free,'blocks',len(orig),'->',len(alive),'surviving masks',sorted(alphabet),flush=True)
    return bs,ps
if __name__=='__main__':run('--cert' in sys.argv)
