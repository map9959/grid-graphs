"""Exact deficit sets for rooted horizontal bands avoiding the forbidden arm."""
from functools import lru_cache
from itertools import product
from hashlib import sha256
import gzip,json
from pathlib import Path
from .tile_family_lp import typ
from .neighbor_strip_pump import cols

raw=Path('target/tile_family_3_5_h6.json.gz').read_bytes()
assert sha256(raw).hexdigest()==json.loads(Path(
    'target/tile_catalogue_proofs/manifest_0_12.json').read_text())['catalogue']
B={(u,v):set(map(tuple,ws)) for u,v,ws in json.loads(gzip.decompress(raw))}
K=38
@lru_cache(maxsize=200000)
def advance(z,m,teeth,cuts,extra_root=False):
    old,pp,flags=z;h=len(pp)-1;p=list(pp)+list(range(h+1,2*h+1))
    tags=list(flags)+[(2 if m>>i&1 else 0)|(1 if cuts>>i&1 else 0) for i in range(h)]
    def root(v):
        while p[v]!=v:v=p[v]
        return v
    def edge(x,y):
        a,b=root(x),root(y)
        if a==b:return False
        p[a]=b;tags[b]|=tags[a];return True
    for i in range(h):
        if old>=0 and (old|m)>>i&1 and not edge(i,h+1+i):return
        if i and m>>(i-1)&3 and not edge(h+i,h+i+1):return
        if m&teeth&(1<<i) and not edge(h+1+i,h):return
    if extra_root and not edge(2*h,h):return
    roots=[root(x) for x in (*range(h+1,2*h+1),h)]
    if any(tags[x]==2 and p[x]==x and x not in roots for x in range(h)):return
    ids={};part=tuple(ids.setdefault(v,i) for i,v in enumerate(roots))
    return m,part,tuple(tags[v] if i==part[i] else 0 for i,v in enumerate(roots))
def transpose(m):
    return sum((m>>(3*a+b)&1)<<(3*b+a) for a,b in product(range(3),repeat=2))

def spectrum(r,H,axis,trace=False,pump_cost=0,vertical=False,join_s=None,require_roots=False):
    # Optional east neighbor: exact exposed column and component partition
    # from joined_arm_budget.phase. The one nonroot marked component has
    # a single exposed, unmarked site at index 3*s+4.
    seam=None if join_s is None else ([6]+[7]*(join_s-1)+[16,16]+[448]*K)[:K]+[192]
    pump=12 if seam is None else join_s+4
    assert seam is None or (vertical and 6<=pump<K-6 and r+H<K-6)
    @lru_cache(None)
    def links(j):
        tabs=[]
        for i in range(r,r+H-1):
            tab={}
            ws=B[typ(i,K),typ(j,K)] if not vertical else (
                tuple(transpose(w[h]) for h in (0,2,1,3)) for w in B[typ(j,K),typ(i,K)])
            for a,b,c,d in ws:
                if any(min(i+di,j+dj,K-i-di,K-j-dj)>=4 and m&16 and m&(40 if (axis==1)!=vertical else 130)
                       for (di,dj),m in zip(product(range(2),repeat=2),(a,b,c,d))):continue
                tab.setdefault((a,b),[]).append((c,d))
            tabs.append(tab)
        pairs={}
        def grow(w,y):
            if len(w)==H:
                if seam is not None:
                    b=tuple(transpose(m) for m in (w[-1],seam[j],y[-1],seam[j+1]))
                    if b not in B[typ(j,K),6]:return
                pairs.setdefault(w,[]).append(y);return
            for a,b in tabs[len(w)-1].get((w[-1],y[-1]),()):grow((*w,a),(*y,b))
        for a,b in tabs[0]:grow((a,),(b,))
        return pairs
    rim=(2 if r==0 else 0)|(1<<(3*H-2) if r+H==K+1 else 0)
    @lru_cache(None)
    def step_at(z,w,j):
        end=j in (0,K)
        for l,m in enumerate(cols(w)):
            cuts=int(r>0)|((1<<(3*H-1)) if r+H<K+1 and seam is None else 0)
            if require_roots:cuts=0
            hit=bool(m>>(3*H-1));x=3*j+l
            if seam is not None and x==3*join_s+4 and not hit:return
            contact=seam is not None and x<3*join_s+2 and (hit or bool(seam[j]>>l&1))
            z=advance(z,m,(1<<(3*H))-1 if l==1 and end else rim,cuts,contact)
            if z is None:break
        return z
    def step(z,w,j):return step_at(z,w,j if seam is not None or j in (0,K) else 6)
    def pos(j):return j if seam is not None or not 6<=j<K-6 else 6
    def loss(w):return 3*H-sum(m.bit_count() for m in w)
    st={}
    for w in links(0):
        z=step((-1,tuple(range(3*H+1)),(0,)*(3*H)+(1,)),w,0)
        if z is not None:st[w,z]=1<<loss(w)
    traces=[]
    for j in range(K):
        if trace:traces.append(st)
        by=links(pos(j));nd={}
        for (w,z),bits in st.items():
            if pump_cost is not None and j==pump and (loss(w)!=pump_cost or w not in by.get(w,()) or step(z,w,j)!=z):continue
            for y in by.get(w,()):
                # At the probe column (eight tiles from the east), forbid
                # 448; then any east suffix starts strictly to its east.
                if not vertical and j+1==K-7 and any(m==448 and 6<=r+h<=K-6 for h,m in enumerate(y)):continue
                if vertical and r+H==K+1 and 6<=j+1<=K-6 and y[-1]==transpose(192):continue
                s=step(z,y,j+1)
                if s is not None and (j+1!=K or 2 not in s[2]):
                    nd[y,s]=nd.get((y,s),0)|(bits<<loss(y))
        st=nd
    total=0
    for b in st.values():total|=b
    if not trace:return total
    def witness(d):
        key=next(v for v,b in st.items() if b>>d&1);path=[key[0]]
        for j in reversed(range(K)):
            y,s=key;d-=loss(y);by=links(pos(j))
            key=next((w,z) for (w,z),b in traces[j].items() if b>>d&1 and
                     (pump_cost is None or j!=pump or (loss(w)==pump_cost and w in by[w] and step(z,w,j)==z)) and
                     y in by.get(w,()) and step(z,y,j+1)==s)
            path.append(key[0])
        assert d==loss(path[-1]);return list(reversed(path))
    return total,witness

def physical(path,r,k,axis,vertical,component_at=None,require_roots=False):
    # Rebuild on actual sites rather than using frontier labels or a solver.
    H=len(path[0]);h=3*H;width=3*k;X=set()
    for j,w in enumerate(path):
        for i,m in enumerate(w):
            X.update((3*i+t//3,3*j+t%3) for t in range(9) if m>>t&1)
            if min(r+i,k-1-r-i,j,k-1-j)>=4:
                assert not(m&16 and m&(40 if (axis==1)!=vertical else 130))
            if vertical and r+i==k-1 and 6<=j<=k-7:assert m!=transpose(192)
            if not vertical and j==k-8 and 6<=r+i<=k-7:assert m!=448
        if j:
            for i in range(H-1):
                b=(path[j-1][i],w[i],path[j-1][i+1],w[i+1])
                u,v=typ(r+i,k-1),typ(j-1,k-1)
                if vertical:u,v=v,u;b=tuple(transpose(b[h]) for h in (0,2,1,3))
                assert b in B[u,v]
    if r==0:
        a,b=(4,1) if vertical else (1,4)
        assert not (X & {(a,b),(a+1,b),(a-1,b),(a,b-1),(a,b+1)})
    seen=set();sealed=0;component=None
    for start in X:
        if start in seen:continue
        q=[start];seen.add(start);degree=teeth=0;cut=False
        for i,j in q:
            marked=(i,j) in X
            teeth+=marked and (j in (1,width-2) or 3*r+i in (1,width-2))
            cut|=(i==0 and r>0) or (i==h-1 and r+H<k)
            for z in ((i-1,j),(i+1,j),(i,j-1),(i,j+1)):
                if 0<=z[0]<h and 0<=z[1]<width and (marked or z in X):
                    degree+=1
                    if z not in seen:q.append(z);seen.add(z)
        assert degree==2*(len(q)-1) and teeth<=1
        if require_roots:assert teeth==1
        if component_at is not None and component_at in q:component=teeth,cut
        if not(teeth or cut):sealed+=1
    result=3*k*H-len(X),sealed
    if component_at is None:return result
    assert component is not None
    return *result,component

def audit(axis,vert):
    @lru_cache(None)
    def band(r,H,c):
        pc=int(not vert and r==0)
        bs,get=spectrum(r,H,axis,True,pc,vert);assert bs>>c&1
        return get(c)
    for t in (0,1,2):
        k=39+14*t;groups=[(0,3,20 if vert else 46)]
        for r in range(3,39,4):
            if r==15:
                groups+=([(7,4,20 if vert else 16)]*3+[(7,2,12 if vert else 10)])*t
            groups.append((r,4,(26 if vert else 24) if r==35 else 19 if vert else 16))
        start=amount=detached=0
        for r,H,c in groups:
            p=band(r,H,c);p=p[:13]+[p[12]]*(14*t)+p[13:]
            d,s=physical(p,start,k,axis,vert);amount+=d;detached+=s;start+=H
        assert start==k and amount==5*k-1+(k-5)//7 and detached==0
        print(axis,'vertical' if vert else 'horizontal','k',k,'deficit',amount,'sealed components',detached,flush=True)

if __name__=='__main__':
    for a,v in product((1,2),(False,True)):audit(a,v)
