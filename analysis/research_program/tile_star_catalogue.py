"""Reuse flat/edge/corner windows across all remaining north-star positions."""
from itertools import product
from functools import lru_cache
from pathlib import Path
import gzip,json,subprocess
from hashlib import sha256
from .tile_family_lp import typ,projected
from .defect_window import table,window,DIR
from .slit_star_transfer import frame_path

def catalogue(n,ds,cert=False):
    from pysat.solvers import Solver
    K=(n-2)//3-1;old=projected(3,5);ref=119;R=38
    reps={tuple(typ(i,R) for i in p):p for p in product(range(R),repeat=2)}
    cache=Path('target/tile_star_catalogues');cache.mkdir(exist_ok=True)
    T=table(ref);marks,path=frame_path(ref,3);allwords={};choices={};conditional={}
    def phase(i,j,d):
        return d-1-3*j if i<=2 and -5<=d-1-3*j<=10 else None
    @lru_cache(None)
    def get(p,ph):
        i,j=reps[p];x,y=1+3*i,1+3*j
        if ph==phase(i,j,5):return old[p]
        dom=set(product(range(max(0,x-6),min(ref,x+12)),range(max(0,y-6),min(ref,y+12))))
        want=ph is not None;col=ph+y if want else -99
        if want:assert all((2+a,col+b) in dom for a,b in ((0,0),*DIR))
        st=cache/f'word_{p[0]}_{p[1]}_{ph}';fn=st.with_suffix('.json.gz')
        if fn.exists():words=[tuple(z) for z in json.loads(gzip.decompress(fn.read_bytes()))]
        else:words=None
        if words is not None:
            if not cert:return words
            check=st.with_suffix('.check')
            if cert=='missing' and check.exists():
                a,b,_,h=check.read_text().split()
                if (a,b,h)==('s','VERIFIED',sha256(fn.read_bytes()).hexdigest()):return words
        def emit(f,bit,flags):
            nonlocal words
            for u in sorted(dom & marks.keys()):f.append([bit(*u)*(1 if marks[u] else -1)])
            vs=[[bit(x+3*h+a,y+3*l+b) for a,b in product(range(3),repeat=2)] for h,l in product(range(2),repeat=2)]
            if words is None:
                words=[]
                with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
                    while s.solve():
                        m=set(s.get_model());words.append(tuple(sum((z in m)<<k for k,z in enumerate(t)) for t in vs))
                        s.add_clause([-z if z in m else z for t in vs for z in t])
                words.sort();fn.write_bytes(gzip.compress(json.dumps(words,separators=(',',':')).encode(),mtime=0))
            if cert:
                for block in words:f.append([z*(-1 if v>>k&1 else 1) for v,t in zip(block,vs) for k,z in enumerate(t)])
                inp=st.with_suffix('.cnf');pr=st.with_suffix('.drat');f.to_file(str(inp))
                with st.with_suffix('.log').open('wb') as fd:assert subprocess.run(['target/cadical/build/cadical',str(inp),str(pr)],stdout=fd).returncode==20
                out=subprocess.run(['target/drat-trim/drat-trim',str(inp),str(pr)],capture_output=True,check=True).stdout
                assert b's VERIFIED' in out;st.with_suffix('.check').write_text('s VERIFIED '+sha256(inp.read_bytes()).hexdigest()+' '+sha256(fn.read_bytes()).hexdigest())
                inp.unlink();st.with_suffix('.log').unlink()
        window(ref,'rim',1,T,want=want,defects={('s',2,col)},root_site=(118,118),orient=path,domain=dom,emit=emit)
        return words
    for i,j in product(range(K),repeat=2):
        p=typ(i,K),typ(j,K);phases={d:phase(i,j,d) for d in ds}
        key=p,tuple(sorted(set(phases.values()),key=repr));choices[i,j]=key
        if key not in allwords:allwords[key]=sorted({z for ph in key[1] for z in get(p,ph)})
        if len(key[1])>1:
            by={ph:set(get(p,ph)) for ph in key[1]}
            conditional[i,j]={z:tuple(d for d,ph in phases.items() if z in by[ph]) for z in allwords[key]}
    print('star catalogue locations',len(allwords),'physical conditional blocks',len(conditional),'windows',get.cache_info().currsize,flush=True)
    return allwords,choices,conditional
if __name__=='__main__':
    import sys
    if '--287' in sys.argv:catalogue(287,range(5,282,3),'missing')
    else:catalogue(245,range(5,192,6),'--cert' in sys.argv)
