"""Stretch the 371 DRAT core, not a satisfying assignment, over two insertions."""
import gzip,json,sys,subprocess
from pathlib import Path
from itertools import product
from .two_gap_329_core import run as decode

OUT=Path('target/core371_lift');CUT=(67,355)
def name(vp,base,n,z):
    ds=range(14,n-14,3);K=len(ds)
    if z<=base:
        u=vp.obj(z)
        return u if u is not None else ('aux',z)
    h=z-base
    if h<=2:return ('frame',) if h==1 else ('axis',)
    if h<=2+K:return ('row',ds[h-3])
    if h<=2+2*K:return ('col',ds[h-3-K])
    a,r=divmod(h-3-2*K,2);i,j=divmod(a,n-4)
    return ('color',i+2,j+2,r)

def setup():
    OUT.mkdir(exist_ok=True)
    def emit(vp,base,last,ids,p):
        tags={z:name(vp,base,371,z) for z in ids}
        assert not any(t[0]=='aux' for t in tags.values())
        with gzip.open(OUT/'ids.json.gz','wt') as fd:json.dump(tags,fd,separators=(',',':'))
    decode(371,emit)

def source():
    with gzip.open(OUT/'ids.json.gz','rt') as fd:tags={int(z):tuple(t) for z,t in json.load(fd).items()}
    with Path('target/two_gap_371_0011_axis_ordinary_linked.core').open() as fd:
        cs=[tuple(map(int,s.split()[:-1])) for s in fd if not s.startswith(('p','c'))]
    return tags,cs

def coord(t,a):
    if t[0] in ('axis','frame'):return None
    if t[0] in ('row','col'):return t[1] if t[0]==('row','col')[a] else None
    return t[1+a]

def move(t,di,dj):
    if t[0] in ('axis','frame'):return t
    if t[0] in ('row','col'):return t[0],t[1]+(di if t[0]=='row' else dj)
    return t[0],t[1]+di,t[2]+dj,*t[3:]

def shifts(xs,cut,fill):
    if not xs:return [0]
    if fill and min(xs)>=cut-4 and max(xs)<=cut+4:return range(0,43,3)
    if max(xs)<cut:return [0]
    if min(xs)>=cut:return [42]
    return []

def lifted(fill=True,cut=CUT):
    tags,cs=source();ids={};out=set()
    for c in cs:
        us=[tags[abs(z)] for z in c]
        steps=[shifts([v for t in us if (v:=coord(t,a)) is not None],cut[a],fill) for a in range(2)]
        for x,y in product(*steps):
            out.add(tuple(sorted((1 if z>0 else -1)*ids.setdefault(move(t,x,y),len(ids)+1) for z,t in zip(c,us))))
    return ids,out

def probe():
    from pysat.solvers import Solver
    for cuts in [(67,355),(67,185),(67,109),(67,262),(270,355),(185,185)]:
        for fill in (False,True):
            names,clauses=lifted(fill,cuts)
            with Solver(name='cadical195',bootstrap_with=clauses) as s:
                s.conf_budget(30000);print(cuts,fill,len(clauses),s.solve_limited(),flush=True)

def target_map():
    from .two_gap_board import run
    tags,_=source();n=413
    def collect(vp,base,path):
        assert vp.top==base
        K=len(range(14,n-14,3));mapping={}
        for t in tags.values():
            for di,dj in product((0,42) if t[0]!='s' else (0,),range(0,43,3)):
                u=move(t,di,dj)
                if u in mapping:continue
                if u[0] in ('frame','axis'):z=base+1+int(u[0]=='axis')
                elif u[0] in ('row','col'):
                    if not 14<=u[1]<n-14:continue
                    z=base+3+(u[1]-14)//3+K*int(u[0]=='col')
                elif u[0]=='color':
                    _,i,j,h=u;z=base+3+2*K+2*((n-4)*(i-2)+j-2)+h
                else:z=vp.obj2id.get(u)
                if z is not None:mapping[u]=z
        # Interior of the horizontal cut may also use intermediate row shifts.
        for t in tags.values():
            if coord(t,0) is None or not 63<=coord(t,0)<=71:continue
            for di,dj in product(range(3,42,3),range(0,43,3)):
                u=move(t,di,dj)
                if u[0]=='row':z=base+3+(u[1]-14)//3
                elif u[0]=='color':
                    _,i,j,h=u;z=base+3+2*K+2*((n-4)*(i-2)+j-2)+h
                else:z=vp.obj2id.get(u)
                if z is not None:mapping[u]=z
        with gzip.open(OUT/'target_ids.gz','wt') as fd:
            for t,z in mapping.items():fd.write(json.dumps([*t,z],separators=(',',':'))+'\n')
        print('translated target IDs',len(mapping))
    sys.argv.extend(['--axis','--stream','--ordinary-bridge','--linked-exits'])
    run(n,0,'0011',collect)

def candidates():
    tags,cs=source()
    with gzip.open(OUT/'target_ids.gz','rt') as fd:
        mapping={tuple(u[:-1]):u[-1] for u in map(json.loads,fd)}
    with (OUT/'candidates.txt').open('w') as fd:
        for c in cs:
            us=[tags[abs(z)] for z in c]
            ys=[v for t in us if (v:=coord(t,0)) is not None];xs=[v for t in us if (v:=coord(t,1)) is not None]
            # Union over aligned local translations throughout the longitudinal
            # bulk. Exact target-clause membership, not the translation
            # heuristic, decides whether to include a clause.
            xx=[0] if not xs or max(xs)<16 else [42] if min(xs)>354 else range(0,43,3)
            for dy,dx in product(shifts(ys,67,True),xx):
                vs=[mapping.get(move(t,dy,dx)) for t in us]
                if all(vs):fd.write(' '.join(map(str,sorted(v if z>0 else -v for v,z in zip(vs,c))))+' 0\n')
def ranks():
    """Layer 0 uses core variables; layer 1 takes all physical variables
    at their sites; subsequent layers thicken that support in grid distance."""
    from .defect_window import table,window
    from .two_gap_329_core import Discard
    from inspect import getclosurevars
    n=413;used=set()
    with (OUT/'shared_413.cnf').open() as fd:
        _,_,nv,_=fd.readline().split();nv=int(nv)
        for l in fd:used.update(abs(v) for v in map(int,l.split()[:-1]))
    def emit(f,bit,flags):
        vp=getclosurevars(bit).nonlocals['vp'];base=vp.top
        dist=[[255]*n for _ in range(n)]
        for z in used:
            t=name(vp,base,n,z)
            if len(t)>=3:dist[t[1]][t[2]]=0
        for i in range(n):
            for j in range(n):
                if i:dist[i][j]=min(dist[i][j],dist[i-1][j]+1)
                if j:dist[i][j]=min(dist[i][j],dist[i][j-1]+1)
        for i in reversed(range(n)):
            for j in reversed(range(n)):
                if i+1<n:dist[i][j]=min(dist[i][j],dist[i+1][j]+1)
                if j+1<n:dist[i][j]=min(dist[i][j],dist[i][j+1]+1)
        rr=bytearray(nv+1);fr=bytearray(nv+1);pr=bytearray(nv+1)
        for z in range(1,nv+1):
            t=name(vp,base,n,z)
            if z not in used and len(t)>=3 and t[0]!='s':rr[z]=min(255,1+dist[t[1]][t[2]])
            if rr[z]:
                fr[z]=rr[z] if t[0]=='face' else 255
                pr[z]=rr[z] if t[0] in ('v','a') else 255
        (OUT/'ranks.bin').write_bytes(rr)
        (OUT/'ranks_face.bin').write_bytes(fr);(OUT/'ranks_primal.bin').write_bytes(pr)
    sites={('s',0,d) for d in range(107,n-107,3)}
    window(n,'rim',n,table(n),matching=True,exit_only=True,emit=emit,clause_sink=Discard(),defects=sites)
if __name__=='__main__':{'setup':setup,'probe':probe,'map':target_map,'candidates':candidates,'ranks':ranks}[sys.argv[1]]()
