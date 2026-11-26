"""Width-independent ordered multiport forest and deficit transfer."""
from collections import defaultdict
from functools import lru_cache
from .component_debt import cols,links,step,typ
from .missing_arm_rim import words
from .western_cut_transfer import BT
from .arm_budget_bands import transpose

@lru_cache(None)
def charts(u,v,offset):
    from pathlib import Path
    import json,gzip,hashlib
    if v>2:return BT[u,v]
    ph=1+3*offset if -2<=offset<=3 else None
    if ph==(1+3*(1-u) if u<=3 else None):return BT[u,v]
    p=Path(f'target/tile_star_catalogues/word_{v}_{u}_{ph}')
    raw=p.with_suffix('.json.gz').read_bytes()
    a,b,_,digest=p.with_suffix('.check').read_text().split()
    assert (a,b,digest)==('s','VERIFIED',hashlib.sha256(raw).hexdigest())
    return {tuple(transpose(w[h]) for h in (0,2,1,3)) for w in json.loads(gzip.decompress(raw))}

def partitions(n):
    states=[()]
    for _ in range(n):
        states=[s+(i,) for s in states for i in range(max(s,default=0)+2)]
    return states

@lru_cache(None)
def incoming(n):
    return tuple(partitions(n))

def glue(L,R,trees,prev,cap,lineage=False):
    # Node 0 is the common perimeter. Each tree's bitmask names its
    # incidences, with disjoint bit ranges for west and east, and its root.
    if len(prev)!=L:return
    p=list(range(1+max(prev,default=0)+len(trees)))
    def rt(i):
        while p[i]!=i:i=p[i]
        return i
    def join(i,j):
        i,j=rt(i),rt(j);p[i]=j;return i!=j
    ends=[None]*R
    for i,t in enumerate(trees,1+max(prev,default=0)):
        if t&2:assert join(0,i)
        for a,prefix in enumerate(prev):
            if t&(4<<a) and not join(i,prefix):return
        for b in range(R):
            if t&(4<<(cap+b)):ends[b]=i
    roots=[rt(i) for i in ends]
    if any(rt(i)!=rt(0) and rt(i) not in roots for i in range(len(p))):return
    ids={rt(0):0}
    following=tuple(ids.setdefault(i,len(ids)) for i in roots)
    if not lineage:return following
    return following,tuple(ids[rt(i)] for i in range(1,1+max(prev,default=0)))

@lru_cache(maxsize=30000)
def lane(state,m,tags):
    old,part,data=state;n=len(part);p=list(part)+list(range(n,2*n));data=list(data)+list(tags)
    def rt(i):
        while p[i]!=i:i=p[i]
        return i
    def join(i,j):
        a,b=rt(i),rt(j);p[a]=b;data[b]|=data[a]
    for i in range(n):
        if old>=0 and (old|m)>>i&1:join(i,i+n)
        if i and m>>(i-1)&3:join(i+n-1,i+n)
    roots=[rt(i) for i in range(n,2*n)];ids={}
    pp=tuple(ids.setdefault(v,i) for i,v in enumerate(roots))
    done=tuple(data[i] for i in range(n) if p[i]==i and i not in roots and data[i]&1)
    return (m,pp,tuple(data[v] if pp[i]==i else 0 for i,v in enumerate(roots))),done

def relation(axis,r,cap=2,phase=None,detail=True,upper=True,span=1,offset=None,drift=0,ends=False,lineage=False,exact=False):
    """All lengths >=39; minimize or maximize deficit per ordered transition.

    Port positions may stretch, but order, row phase and hop endpoints
    (in detail mode) must match. Costs are exact extremal values in the
    union over lengths, not a claim of common fills for different columns.
    """
    K=38;H=span+2;n=3*span;rim=7<=r and r+span<=32
    north,south=words(H,True,phase),words(H,False)
    @lru_cache(None)
    def by(j):
        v=typ(j,K);t=links(H,r,v,tuple(min(x,K-x)>=4 for x in (j,j+1)),axis)
        if v>2 or offset is None:return t
        out=defaultdict(list)
        for w,ys in t.items():
            for y in ys:
                if all((w[h],y[h],w[h+1],y[h+1]) in charts(typ(i,K),v,offset+r-i)
                       for h,i in enumerate(range(r-1,r+H-2)) if 0<=i<K):out[w].append(y)
        return out
    def upd(out,key,v):
        if key not in out or (v>out[key] if upper else v<out[key]):out[key]=v
    @lru_cache(maxsize=40000)
    def col(w,f,L,R,counts,delta,end,final):
        complete=[]
        for b,m in enumerate(cols(w)):
            c=(m>>3)&((1<<n)-1)
            tags=[(c>>i&1)*(1+2*(end and b==1 or 3*r+i in (1,115))) for i in range(n)]
            for side,x in enumerate(range(3,n+4,3)):
                code=None
                if m>>(x-1)&1 and m>>x&1:code=0
                elif m>>(x-2)&1 and not m>>(x-1)&1 and m>>x&1:code=1
                elif m>>(x-1)&1 and not m>>x&1 and m>>(x+1)&1:code=2
                if code is None:continue
                if 0<side<span:
                    count=counts[side-1]+1
                    if count>cap:return
                    counts=counts[:side-1]+(count,)+counts[side:]
                    continue
                ports=R if side else L
                if len(ports)==cap:return
                i=(n-2 if code==1 else n-1) if side else int(code==2)
                assert c>>i&1
                tags[i]|=4<<(bool(side)*cap+len(ports))
                ports=ports+((3*b+code if detail else 0),)
                if side:R=ports
                else:L=ports
            if drift:
                delta=tuple(max(-drift,min(drift,v+(len(L)>i)-(len(R)>i))) for i,v in enumerate(delta))
            f,ds=lane(f,c,tuple(tags));complete.extend(ds)
        if final:complete.extend(t for t in f[2] if t&1)
        if 1 in complete:return
        return f,L,R,counts,delta,tuple(t for t in complete if t!=3)
    base=-1,tuple(range(3*H+1)),(0,)*(3*H)+(1,)
    core=-1,tuple(range(n)),(0,)*n;st={}
    def add(out,w,z,f,L,R,counts,delta,done,j,cost,top):
        if rim and j==K and w not in south:return
        v=step(z,w,j in (0,K),r)
        if v is None or j==K and 2 in v[2]:return
        res=col(w,f,L,R,counts,delta,j in (0,K),j==K)
        if res is None:return
        g,A,B,cs,d,more=res
        value=cost+n-sum(x.bit_count() for x in w[1:-1])
        upd(out,(w,v,g,A,B,cs,d,tuple(sorted(done+more)),top,value if exact else None),value)
    for w in by(0):
        if rim and phase==-4 and any(m!=6 for m in w):continue
        if not rim or w in north:add(st,w,base,core,(),(),(0,)*(span-1),(0,)*cap if drift else (),(),0,0,
                                      (w[:2],w[-2:]) if ends else ())
    def move(src,j):
        nd={};tab=by(j)
        for (w,z,f,L,R,cs,delta,done,top,_),v in src.items():
            for y in tab[w]:add(nd,y,z,f,L,R,cs,delta,done,j+1,v,top)
        return nd
    for j in range(K):
        st=move(st,j)
        if j==18:
            delta=st.copy()
            for _ in range(100):
                delta={s:v for s,v in move(delta,j).items()
                       if s not in st or (v>st[s] if upper else v<st[s])}
                if not delta:break
                st.update(delta)
            else:raise ValueError('no verified length closure')
    out={}
    @lru_cache(None)
    def legal(l,r,trees):
        return tuple((p,q) for p in incoming(l) if (q:=glue(l,r,trees,p,cap,lineage)) is not None)
    for (w,_,_,L,R,_,delta,trees,top,_),v in st.items():
        for p,q in legal(len(L),len(R),trees):
            if lineage:q,heirs=q
            key=((L,p),(R,q))
            if ends:key=((L,p,top[0]+w[:2] if r else ()),(R,q,top[1]+w[-2:] if r+span<=K else ()))
            if lineage:key=(*key,heirs)
            if exact:key=(*key,v)
            upd(out,(*key,delta) if drift else key,v)
    return out

if __name__=='__main__':
    import sys
    a,r,h=map(int,sys.argv[1:4])
    b=relation(a,r,h,detail='--detail' in sys.argv)
    print(a,r,h,'transitions',len(b),'max cost',max(b.values(),default=None))
