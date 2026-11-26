"""Direct physical replay of the unoriented 1-gap charge/run identity."""
from collections import Counter
from itertools import product
from pathlib import Path
import sys
from .defect_window import table,DIR
from .odd_frames import frame

def types(n):
    T,_,S=table(n);ds=tuple(range(4))
    depth=lambda i,j:min(i,j,n-1-i,n-1-j)
    prefs={};pairs=set()
    for i,j in product(range(3,n-3),repeat=2):
        t=T(0,i,j)
        if t not in prefs:
            q=[S(t,ds,d,False,False) for d in ds];s=S(t,ds,-1,True,False)
            prefs[t]=[v[1]==0 for v in q]
            for mask in range(32):
                nb={d for d in ds if mask&(2<<d)}
                if any((d+1)%4 in nb for d in nb):continue
                if mask&1:assert s[mask]==576
                for d in ds:
                    expected=(d in nb or bool(mask&1 and prefs[t][d]))
                    assert (q[d][mask]==0)==expected
        for d,(a,b) in enumerate(DIR[:2]):
            x,y=i+2*a,j+2*b
            if depth(x,y)>=3:pairs.add((t,d,T(0,x,y)))
    for t,d,u in pairs:assert prefs[t][d]==prefs[u][d+2]
    # Explicitly check that every depth-two tooth has a perimeter foot.
    for w in product((1,3),repeat=3):
        m=frame(n,(0,*w))
        for i,j in product(range(2,n-2),repeat=2):
            if depth(i,j)==2:
                assert any(depth(i+2*a,j+2*b)==0 and m[i+2*a,j+2*b] for a,b in DIR)
    print(n,len(prefs),'bulk types; sink charge 576;',len(pairs),'join type/direction pairs all symmetric; all eight frames have feet')
    return prefs,pairs

def audit(rows):
    n=len(rows);k=(n-2)//3;U=3*k*k+7*k-(k-5)//7;T,P,S=table(n)
    sites=list(product(range(n),repeat=2))
    X={u for u in sites if rows[u[0]][u[1]]=='#'}
    frames=[frame(n,(0,*w)) for w in product((1,3),repeat=3)]
    m,=[m for m in frames if all((u in X)==bool(b) for u,b in m.items())]
    dep=lambda u:min(*u,n-1-u[0],n-1-u[1])
    nb=lambda u,d:(u[0]+DIR[d][0],u[1]+DIR[d][1])
    ds={u:tuple(d for d in range(4) if dep(nb(u,d))>=0) for u in sites}
    marked=lambda u:[d for d in ds[u] if nb(u,d) in X]
    path={(0,0):-1};todo=list(path)
    for u in todo:
        for d in ds[u]:
            v=nb(u,d)
            if dep(v)==0 and v not in path and (u in X or v in X):
                path[v]=(d+2)%4;todo.append(v)
    iso,=[u for u in sites if u not in X and not marked(u)]
    assert dep(iso)==2 and min(iso)==2 and 5<=max(iso)<=n-6 and max(iso)%3==2
    out={u:set() for u in sites}
    # Fix all leaves, all nonbulk parents, and every unmarked join.
    for u in sites:
        if u in path:
            if path[u]>=0:out[u].add(path[u])
        elif u==iso:continue
        elif u in X:
            if dep(u)==2:
                feet=[d for d in ds[u] if dep(nb(nb(u,d),d))==0 and nb(nb(u,d),d) in X]
                d,=feet;out[u].add(d)
            else:assert dep(u)>=3
        else:
            neighbors=marked(u)
            if len(neighbors)==1:d,=neighbors
            else:
                a,b=neighbors;assert (a-b)%4==2
                # Go toward the boundary tooth, if any. Otherwise both
                # directions work; pick one deterministically.
                d=min(neighbors,key=lambda d:dep(nb(u,d)))
            out[u].add(d)
    E=A=0;pred={};cycle_rank=0
    def rt(p):
        while p in pred:
            if pred[p] in pred:pred[p]=pred[pred[p]]
            p=pred[p]
        return p
    for u in sites:
        for d in (0,1):
            v=nb(u,d)
            if d not in ds[u] or not (u in X or v in X):continue
            E+=1;A+=int(u in X and v in X)
            x,y=rt(u),rt(v)
            if x==y:cycle_rank+=1
            else:pred[x]=y
            ab=d in out[u];ba=d+2 in out[v]
            assert not(ab and ba),(u,v)
            if ab or ba:continue
            if u in X and dep(u)>=3:out[u].add(d)
            else:assert v in X and dep(v)>=3;out[v].add(d+2)
    charged=0;dists=Counter()
    for u in sites:
        dirs=ds[u];i,j=u
        if max(u)<n-2:
            assert not P(T(1,i,j))[sum(((i+a,j+b) in X)<<(3*a+b) for a,b in product(range(3),repeat=2))]
        mask=int(u in X)+sum((nb(u,d) in X)<<(h+1) for h,d in enumerate(dirs))
        def charge(d,rawsink=False):
            return S(T(0,i,j),dirs,d,rawsink or u==(0,0),len(dirs)==2)[mask]
        if u in X and dep(u)>=3:
            assert charge(-1,True)==576 and all(charge(d)==0 for d in out[u])
            charged+=576*(1-len(out[u]));dists[len(out[u])]+=1
        else:
            arrow,=out[u] or {-1}
            assert charge(arrow)==72*(u==iso)
            charged+=charge(arrow)
    assert charged==72+576*(n*n-2-E)==72+1008*(U-len(X))
    r=len(X)-A;rstar=8*n//7-2
    assert 5*(len(X)-U)+4*(r-rstar)==0
    comps=n*n-len(pred)-1 # omit the one isolate
    assert cycle_rank==E-n*n+comps+1
    print(n,'star',iso,'marks',len(X),'runs',r,'forced edges',E,'signed charge',charged,'nontrivial components',comps,'cycle rank',cycle_rank,'bulk marked outdegrees',dict(sorted(dists.items())))
if __name__=='__main__':
    if '--types' in sys.argv:assert types(119)==types(203)
    elif '--examples' in sys.argv:
        import gzip
        for name in ('cyclic','detached'):
            f=Path(__file__).with_name('one_gap_projection_examples')/f'203_{name}.txt.gz'
            audit(gzip.decompress(f.read_bytes()).decode('ascii').splitlines())
    else:
        for f in sys.argv[1:]:audit(Path(f).read_text().splitlines())
