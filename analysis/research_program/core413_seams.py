"""Parametric cut tests: note that a cut drops, never identifies, interiors."""
from pathlib import Path
from itertools import product
import gzip,json,sys,subprocess
from pysat.solvers import Solver
from .two_gap_core_lift import name
from .two_gap_329_core import run as decode

D=Path('target/core413_uniform');SRC=Path('target/core371_lift/halo_1_primal.core')
def setup():
    D.mkdir(exist_ok=True)
    def save(vp,base,last,ids,_):
        with gzip.open(D/'names.gz','wt') as fd:json.dump({z:name(vp,base,413,z) for z in ids},fd)
    decode(413,save)
def source():
    with gzip.open(D/'names.gz','rt') as fd:tags={int(z):tuple(t) for z,t in json.load(fd).items()}
    with SRC.open() as fd:
        cs=[tuple(map(int,l.split()[:-1])) for l in fd if not l.startswith(('c','p'))]
    return tags,cs
def position(t,a):
    if t[0] in ('aux','axis','frame','s','col','row'):
        return t[1] if t[0]==('row','col')[a] else None
    return t[1+a]
def bounds(tags,cs):
    boxes=[]
    for c in cs:
        ts=[tags[abs(v)] for v in c]
        # s has a site in a local star clause. Counter clauses, however,
        # refer to a list of eligible exits, not physical edges in a seam.
        local=any(t[0] not in ('s','aux','axis','frame') for t in ts)
        box=[]
        for a in (0,1):
            xs=[v for t in ts if (v:=(t[1+a] if local and t[0]=='s' else position(t,a))) is not None]
            box+= [min(xs),max(xs)] if xs else [1,0]
        boxes.append(box)
    return boxes
def probe():
    ts,cs=source();b=bounds(ts,cs)
    for ys,xs in (([193],[]),([],[17]),([],[396]),([],[17,396]),([193],[17,396]),([193],[206])):
        keep=[c for c,(i,j,k,l) in zip(cs,b) if not any(i<y<=j for y in ys) and not any(k<x<=l for x in xs)]
        with Solver(name='cadical195',bootstrap_with=keep) as s:
            s.conf_budget(15000);print(ys,xs,len(keep),s.solve_limited(),flush=True)

def residue_test(row,left,right,budget):
    """Do not demand existence of a short filling between the cut ends."""
    ts,cs=source();bs=bounds(ts,cs)
    keep=[c for c,(i,j,k,l) in zip(cs,bs) if not i<row<=j and not any(k<x<=l for x in (left,right))]
    flags={t[2]:v for v,t in ts.items() if t[0]=='s'}
    assert sorted(flags)==list(range(107,306,3))
    dead=[];ans={}
    with Solver(name='cadical195',bootstrap_with=keep) as s:
        for d in sorted(flags):
            s.conf_budget(budget)
            r=s.solve_limited(assumptions=[flags[d],*[-z for e,z in flags.items() if e!=d]])
            ans[d]=str(r)
            if r is False:dead.append(d)
    print('cut',row,left,right,'pending',dead,'SAT',list(ans.values()).count('True'),'unknown',list(ans.values()).count('None'),flush=True)
    if dead:
        p=D/f'seam_{row}_{left}_{right}.cnf';pr=p.with_suffix('.drat')
        # Keep the whole candidate exit set free except for the checked union.
        # Reinstate pairwise uniqueness explicitly, since the trimmed core
        # need not have preserved the whole sequential counter.
        vs=list(flags.values());clauses=keep+[[-v,-w] for j,v in enumerate(vs) for w in vs[j+1:]]+[[flags[d] for d in dead]]
        with p.open('w') as fd:
            print('p cnf',2716317,len(clauses),file=fd)
            for c in clauses:print(*c,0,file=fd)
        with p.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t','180',str(p),str(pr)],stdout=fd).returncode
        if rc==20:
            data=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],check=True,capture_output=True).stdout
            assert b's VERIFIED' in data;p.with_suffix('.check').write_bytes(data);p.with_suffix('.json').write_text(json.dumps(dead)+'\n');print('s VERIFIED',len(dead))
        else:assert rc==0;print('UNKNOWN union')

def locations():
    from array import array
    n=413
    def emit(vp,base,last,ids,p):
        # Two 16-bit, 1-based coordinates; zero in an unused dimension.
        # Exits keep their position; counter auxiliaries have neither.
        v=array('I',[0])
        for z in range(1,2716318):
            t=name(vp,base,n,z)
            x,y=((1+t[1],1+t[2]) if len(t)>=3 else
                 (1+t[1],0) if t[0]=='row' else (0,1+t[1]) if t[0]=='col' else (0,0))
            v.append((x<<16)|y)
        (D/'loc.bin').write_bytes(v.tobytes())
        marks=array('I',(vp.obj2id['v',i,j] for i,j in product(range(n),repeat=2)))
        (D/'marks.bin').write_bytes(marks.tobytes())
        arcs=array('I',(vp.obj2id.get(('a',i,j,s),0) for i,j,s in product(range(n),range(n),range(4))))
        (D/'arcs.bin').write_bytes(arcs.tobytes())
        rim={}
        for i,j in product(range(n),repeat=2):
            if min(i,j,n-1-i,n-1-j) in (0,2):
                rim[f'{i},{j}']=[vp.obj2id.get(('a',i,j,k),0) for k in range(4)]
        with gzip.open(D/'rim.gz','wt') as fd:json.dump(rim,fd)
    decode(413,emit)

if __name__=='__main__':
    if sys.argv[1]=='exits':residue_test(*map(int,sys.argv[2:]))
    else:{'setup':setup,'probe':probe,'locations':locations}[sys.argv[1]]()
