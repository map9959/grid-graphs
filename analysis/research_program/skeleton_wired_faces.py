"""Coarse-face laws when every junction lies in a single skeleton component."""
from collections import defaultdict,Counter
from functools import lru_cache
from itertools import product
from .four_square import masks4
from .patch_square import trans,SYM,MASKS
from .skeleton_cross_rank import DSU


@lru_cache(None)
def face_masks():
    allm=masks4();classes=defaultdict(dict);valid={}
    inner=sum(1<<i for i in (5,6,9,10));ports=[i for i in range(16) if not inner>>i&1]
    mids=[(i,j) for i in range(16) for j in
          ([i+1] if i%4<3 else [])+([i+4] if i<12 else [])]
    for mask in allm:
        sk=mask&~inner;d=DSU(16)
        for u,v in mids:
            if (sk>>u|sk>>v)&1:assert d.join(u,v)
        for j in (3,12,15):d.join(0,j)
        for u,v in mids:
            if (mask>>u|mask>>v)&1 and not (sk>>u|sk>>v)&1 and not d.join(u,v):break
        else:
            p=sum(1<<(i*12+j) for i,v in enumerate(ports) for j in range(i)
                  if d.root(v)==d.root(ports[j]))
            f=(mask&inner).bit_count()
            classes[sk][p]=max(classes[sk].get(p,0),f)
            valid[mask]=(sk,p,f)
    return {m:allm[m] for m,(sk,p,f) in valid.items()
            if not any(q&~p==0 and z>f for q,z in classes[sk].items())}


def add_faces(ns,A,b,base,d,w,cd):
    S=base-3
    def ax(i,s,h):return i if i<h else 2*h+3+i-s if i>=s-h else h+(i-h)%3
    def pos(i,j,s,h,k):
        clip=lambda t:max(-k,min(k,t))
        return tuple((ax(a,s,h),ax(c,s,h),clip(a-c),clip(a+c+1-s)) for g in range(8)
                     for a,c in [trans(i,j,s,g)])
    reps={};child=defaultdict(dict)
    for i,j in product(range(0,S,3),repeat=2):
        p=pos(i,j,S,cd,0);reps[p[0]]=p
        for t,(u,v) in enumerate(product(range(2),repeat=2)):
            q=pos(i+u,j+v,S+1,d+3,w+5);child[p[0],t][q[0]]=q
    ms=face_masks();seen=set()
    for tag,p in reps.items():
        gs=[defaultdict(Counter) for _ in range(4)]
        for m,(sub,imgs) in ms.items():
            atom=('wiredFace',min(zip(p,imgs)));x=ns.setdefault(atom,'f'+str(len(ns)))
            for t,z in enumerate(sub):gs[t][z][x]+=1
        for t in range(4):
            for z in MASKS:
                c=gs[t][z].copy()
                for q in child[tag,t].values():c[ns['p',min(zip(q,SYM[z]))]]-=1
                row=tuple(sorted(c.items()))
                if row not in seen:seen.add(row);A.append((row,'='));b.append(0)
