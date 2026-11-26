"""Can a whole interior annulus of a residue-one forest carry zero dual charge?"""
from itertools import product,combinations
from pathlib import Path
from hashlib import file_digest
import subprocess,sys
from .diagonal_score import data,cover,DIR

def test(n,r,H,sec):
    from pysat.formula import CNF,IDPool
    pos,P,S,scale,budget=data(n,0);strip='--strip' in sys.argv
    dom={(i,j) for i,j in product(range(n),repeat=2) if (r<=j<r+H if strip else r<=min(i,j,n-1-i,n-1-j)<r+H)}
    assert r>=1 and (r+H<n-1 if strip else n-2*(r+H)>2)
    pool=IDPool();f=CNF()
    def mark(u):return pool.id(('v',*u))
    def arc(u,d):return pool.id(('a',*u,d))
    def nb(u,d):return u[0]+DIR[d][0],u[1]+DIR[d][1]
    def zero(vs,q,guard=()):
        for m,v in cover(tuple(z!=0 for z in q)):
            f.append([*guard,*[(-z if v>>k&1 else z) for k,z in enumerate(vs) if m>>k&1]])
    for u in sorted(dom):
        i,j=u;sq=[(i+a,j+b) for a,b in product(range(3),repeat=2)]
        if all(p in dom for p in sq):zero(list(map(mark,sq)),P(pos(i,j,1)))
        ds=[d for d in range(4) if nb(u,d) in dom];ids=[arc(u,d) for d in ds]
        if '--no-through' in sys.argv:
            assert strip
            c=pool.id(('component',*u))
            if i in (0,n-1):f.append([c if i else -c])
            for d in (0,1):
                v=nb(u,d)
                if v not in dom:continue
                t=pool.id(('component',*v))
                for z in (mark(u),mark(v)):f.extend([[-z,-c,t],[-z,c,-t]])
        for a,b in combinations(ids,2):f.append([-a,-b])
        if all(nb(u,d) in dom or not all(0<=a<n for a in nb(u,d)) for d in range(4)):
            tab=S(pos(i,j,0),tuple(ds),False);vs=[mark(u)]+[mark(nb(u,d)) for d in ds]
            for d in (-1,*ds):zero(vs,tab[d],ids if d<0 else [-arc(u,d)])
        for d in ds:
            v=nb(u,d);a=arc(u,d);b=arc(v,(d+2)%4)
            if d<2:f.extend([[-a,-b],[-mark(u),a,b],[-mark(v),a,b],[-a,mark(u),mark(v)],[-b,mark(u),mark(v)]])
            for e in range(4):
                if e==(d+2)%4 or nb(v,e) not in dom:continue
                x=pool.id(('sheet',*u));y=pool.id(('sheet',*v))*(-1 if abs(d-e)==3 else 1)
                f.extend([[-a,-arc(v,e),-x,y],[-a,-arc(v,e),x,-y]])
    cross='--root-cross' in sys.argv
    if cross:
        assert strip
        # A tree path between the two northern roots contains a subpath
        # from the left edge of this strip to the right. On it the two
        # rootings give opposite directions, even across a free edge.
        old=f.clauses.copy();mapping={i:(i if pool.obj(i)[0]=='v' else pool.id(('copy',i))) for i in range(1,pool.top+1)}
        f.extend([[mapping[abs(z)]*(1 if z>0 else -1) for z in c] for c in old])
        starts=[];ends=[]
        def one(ls):
            for a,b in combinations(ls,2):f.append([-a,-b])
        for u in sorted(dom):
            incoming=[];outgoing=[];ds=[d for d in range(4) if nb(u,d) in dom]
            for d in ds:
                v=nb(u,d);z=pool.id(('path',*u,d));outgoing.append(z);incoming.append(pool.id(('path',*v,(d+2)%4)))
                for a in (mark(u),mark(v)):
                    f.append([-z,-a,mapping[arc(u,d)]]);f.append([-z,-a,arc(v,(d+2)%4)])
                for e in range(4):
                    if e!=d and nb(u,e) in dom:f.append([-z,-mapping[arc(u,e)]])
                    if e!=(d+2)%4 and nb(v,e) in dom:f.append([-z,-arc(v,e)])
            if u[1]==r:
                z=pool.id(('enter',*u));incoming.append(z);starts.append(z)
            if u[1]==r+H-1:
                z=pool.id(('exit',*u));outgoing.append(z);ends.append(z)
            one(incoming);one(outgoing)
            for z in incoming:f.append([-z,*outgoing])
            for z in outgoing:f.append([-z,*incoming])
        for ls in (starts,ends):f.append(ls);one(ls)
    stem=Path(f'target/sector_clean_'+('track' if strip else 'ring')+f'_{n}_{r}_{H}'+('_deep' if '--deep' in sys.argv else '')+('_cut' if '--no-through' in sys.argv else '')+('_cross' if cross else ''));fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
    f.to_file(str(fn))
    with stem.with_suffix('.log').open('wb') as o:s=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(fn),str(pr)],stdout=o).returncode
    with fn.open('rb') as src:sha=file_digest(src,'sha256').hexdigest()
    if s==20:
        rep=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True,check=True).stdout
        assert b's VERIFIED' in rep;stem.with_suffix('.check').write_bytes(rep);print('positive charge necessary; s VERIFIED',n,r,H,scale,sha)
    elif s==10:
        model={int(z) for l in stem.with_suffix('.log').read_text().splitlines() if l.startswith('v ') for z in l[2:].split()}
        X={u for u in dom if mark(u) in model};par={}
        def rt(u):
            while u in par:u=par[u]
            return u
        E=0
        for u in dom:
            ds=tuple(d for d in range(4) if nb(u,d) in dom)
            if all(nb(u,d) in dom or not all(0<=a<n for a in nb(u,d)) for d in range(4)):
                q=S(pos(*u,0),ds,False);m=int(u in X)+sum((nb(u,d) in X)<<(h+1) for h,d in enumerate(ds))
                for second in range(1+int(cross)):
                    outs=[d for d in ds if (mapping[arc(u,d)] if second else arc(u,d)) in model]
                    assert len(outs)<=1 and q[outs[0] if outs else -1][m]==0
            sq=[(u[0]+a,u[1]+b) for a,b in product(range(3),repeat=2)]
            if all(v in dom for v in sq):assert P(pos(*u,1))[sum((v in X)<<k for k,v in enumerate(sq))]==0
            for d in (0,1):
                v=nb(u,d)
                if v in dom and (v in X or u in X):
                    a,b=rt(u),rt(v);assert a!=b;par[a]=b;E+=1
        if '--no-through' in sys.argv:assert not ({rt((0,j)) for j in range(r,r+H)}&{rt((n-1,j)) for j in range(r,r+H)})
        if cross:
            u,=[v for v in dom if v[1]==r and pool.id(('enter',*v)) in model];seen=set()
            while pool.id(('exit',*u)) not in model:
                assert u not in seen;seen.add(u)
                d,=[d for d in range(4) if nb(u,d) in dom and pool.id(('path',*u,d)) in model];v=nb(u,d)
                assert (mapping[arc(u,d)] in model)==(u in X or v in X)==(arc(v,(d+2)%4) in model)
                u=v
            assert u[1]==r+H-1
            print('opposite-root path replayed, length',len(seen))
        print('clean strip SAT' if strip else 'clean annulus SAT',n,r,H,'marks',len(X),'forced edges',E,'cycle rank 0',sha)
    else:print('UNKNOWN',n,r,H,sha)
if __name__=='__main__':test(*map(int,sys.argv[1:5]))
