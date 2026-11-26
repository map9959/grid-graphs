"""Amortize nonperiodic column losses by the actual change in component debt."""
from collections import defaultdict
from functools import lru_cache
from .arm_budget_bands import advance,cols
from .western_cut_transfer import BT,typ,transpose
from .missing_arm_rim import words

@lru_cache(None)
def star_union(u,v):
    from pathlib import Path
    import gzip,json
    from hashlib import sha256
    out=set(BT[u,v])
    if v<=2:
        for ph in [None,*range(-5,11,3)]:
            if ph is not None and (u<6 and u+(ph-1)//3<1 or u>6 and (ph-1)//3>12-u):
                continue
            if ph==(1+3*(1-u) if u<=3 else None):continue
            p=Path(f'target/tile_star_catalogues/word_{v}_{u}_{ph}')
            raw=p.with_suffix('.json.gz').read_bytes()
            a,b,_,hh=p.with_suffix('.check').read_text().split()
            assert (a,b,hh)==('s','VERIFIED',sha256(raw).hexdigest())
            out.update(tuple(transpose(w[i]) for i in (0,2,1,3)) for w in json.loads(gzip.decompress(raw)))
    return out

@lru_cache(None)
def links(H,r,v,deep,axis):
    tabs=[];out=defaultdict(list);K=38
    for i in range(r-1,r+H-2):
        tab=defaultdict(list);tabs.append(tab)
        if not 0<=i<K:continue
        for a,b,c,d in star_union(typ(i,K),v):
            if any(ok and min(x,K-x)>=4 and m&16 and m&(130 if axis==1 else 40)
                   for ok,x,m in zip(deep*2,(i,i,i+1,i+1),(a,b,c,d))):continue
            tab[a,b].append((c,d))
    if r==0:
        tabs[0][0,0]=list(tabs[1])
    if r+H-3==K:
        for ps in tabs[-2].values():
            for p in ps:tabs[-1][p]=[(0,0)]
    def grow(w,y):
        if len(w)==H:out[w].append(y);return
        for a,b in tabs[len(w)-1][w[-1],y[-1]]:grow(w+(a,),y+(b,))
    for a,b in list(tabs[0]):grow((a,),(b,))
    return out

@lru_cache(None)
def step(z,w,end,r):
    n=3*len(w)
    teeth=sum(1<<i for i in range(n) if 3*(r-1)+i in (1,115))
    cuts=int(r>1)|((1<<(n-1)) if r+len(w)-2<38 else 0)
    for l,m in enumerate(cols(w)):
        z=advance(z,m,(1<<n)-1 if end and l==1 else teeth,cuts)
        if z is None:break
    return z

@lru_cache(None)
def west_joins(y):
    # Transverse axial hops across the west edge of the middle tile.
    # No diagonal contacts are possible. A two-step hop skips an
    # unmarked site only; it must not duplicate two adjacent edges.
    return sum(((m>>2)&(m>>3)&1)+((m>>1)&~(m>>2)&(m>>3)&1)
               +((m>>2)&~(m>>3)&(m>>4)&1) for m in cols(y))

@lru_cache(None)
def retire(state,mask,west,east,tooth):
    """Inside the measured block only. Keep contact bits per actual tree."""
    old,part,tags=state;n=len(part)
    p=list(part)+list(range(n,2*n));t=list(tags)
    for i in range(n):
        m=(mask>>i)&1
        t.append(m*(1+2*((west>>i)&1)+4*((east>>i)&1)+8*((tooth>>i)&1)))
    def root(i):
        while p[i]!=i:i=p[i]
        return i
    def join(i,j):
        a,b=root(i),root(j);p[a]=b;t[b]|=t[a]
    for i in range(n):
        if old>=0 and (old|mask)>>i&1:join(i,n+i)
        if i and mask>>(i-1)&3:join(n+i-1,n+i)
    roots=[root(i+n) for i in range(n)];ids={}
    pp=tuple(ids.setdefault(v,i) for i,v in enumerate(roots))
    done=[t[i] for i in range(n) if i==p[i] and i not in roots and t[i]&1]
    return (mask,pp,tuple(t[v] if pp[i]==i else 0 for i,v in enumerate(roots))),tuple(done)

@lru_cache(None)
def contacts(state,w,end,r):
    n=3*(len(w)-2);full=(1<<n)-1;done=[]
    for l,m in enumerate(cols(w)):
        c=(m>>3)&full
        left=int(bool(m&6)) | (2 if m&4 and not c&1 else 0)
        right=((1<<(n-1)) if (m>>(n+3))&3 else 0)|(
            (1<<(n-2)) if (m>>(n+3))&1 and not c>>(n-1) else 0)
        teeth=sum(1<<i for i in range(n) if 3*r+i in (1,115))
        state,ds=retire(state,c,left,right,full if end and l==1 else teeth);done.extend(ds)
    return state,tuple(done)

def bound(axis,price,r=7,phase=None,long=False,rate=1,traffic=None):
    """Lower bound on three-column loss + change in live classes - price*births."""
    h=1;H=3;K=38
    north=words(H,True,phase);south=words(H,False)
    use_rim=r>=7 and r+h<=32
    def by(j):return links(H,r,typ(j,K),tuple(min(x,K-x)>=4 for x in (j,j+1)),axis)
    def cost(y):
        a=y[0] if r else y[1];b=y[-1] if r+h<=K else y[-2]
        if traffic is not None:return y[1].bit_count()-3-rate*west_joins(y)
        return 9-y[1].bit_count()-a.bit_count()-b.bit_count()-rate*west_joins(y)
    @lru_cache(None)
    def ports(seen,w):
        if traffic is None:return 0,0
        l=west_joins(w)
        b=west_joins(tuple((m>>6|(m&56)|(m&7)<<6) for m in reversed(w)))
        after=seen|int(l>0)|(int(b>0)<<1)
        return after,traffic*(l+b-after.bit_count()+seen.bit_count())
    base=-1,tuple(range(3*H+1)),(0,)*(3*H)+(1,)
    cbase=-1,tuple(range(h*3)),(0,)*(h*3)
    def observe(f,w,end,final):
        f,ds=contacts(f,w,end,r)
        if final:ds+=tuple(v for v in f[2] if v&1)
        if 1 in ds:return None,0
        return f,rate*sum(not(v&8) for v in ds)-price*ds.count(5)
    st={}
    ell=1 if long is True else long
    for w in by(0):
        if use_rim and w not in north or long is not False and w[ell]!=6:continue
        z=step(base,w,True,r)
        f,d=observe(cbase,w,True,False)
        p,credit=ports(0,w)
        if z is not None and f is not None:st[w,z,f,p]=cost(w)+d+credit
    def advance_layer(st,j):
        tab=by(j);nd={};end=j==K-1
        for (w,z,f,p),val in st.items():
            for y in tab[w]:
                if end and use_rim and y not in south:continue
                if long is not False and (j+1<13 and y[ell]!=7 or j+1>K-12 and y[ell]!=(192 if end else 448)):continue
                v=step(z,y,end,r)
                if v is not None and (not end or 2 not in v[2]):
                    g,dc=observe(f,y,end,end)
                    if g is None:continue
                    pp,credit=ports(p,y)
                    key=y,v,g,pp;d=val+cost(y)+dc+credit
                    if key not in nd or d<nd[key]:nd[key]=d
        return nd
    stop=K-12 if long is not False else K-6
    mid=18
    for j in range(stop):st=advance_layer(st,j)
    # Shortest path over all nonnegative insertion counts; verify
    # the attained vector is a lower sub-invariant of the 14-step map.
    for _ in range(20):
        later=st
        for _ in range(14):later=advance_layer(later,mid)
        assert st.keys()==later.keys()
        if all(later[x]>=v for x,v in st.items()):break
        st={x:min(v,later[x]) for x,v in st.items()}
    else:raise AssertionError('no verified stationary lower bound')
    for j in range(stop,K):st=advance_layer(st,j)
    return min(st.values())
if __name__=='__main__':
    import sys
    print(bound(*map(int,sys.argv[1:])))
