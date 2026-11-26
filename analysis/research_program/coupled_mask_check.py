"""Independent uncapped support replay. Construct two physical half-forests
from opposite ends of a strip and join their boundary partitions at a plaquette.
No backward traversal of the native solver's search graph is used.
"""
from functools import lru_cache
from collections import defaultdict
from .coupled_mask_grid import instance
from .arm_budget_bands import advance,transpose
from .component_debt import cols

class Pool:
    def __init__(self):self.items=[];self.ids={}
    def intern(self,v):
        k=self.ids.get(v)
        if k is None:k=len(self.items);self.items.append(v);self.ids[v]=k
        return k

def checker(k,h,hor,edge,pool,q=None,omit=0,along=(),across=(),block=1,*,stride=None,ends=3,rootmask=0,rootfrom=None,sealed=0):
    if stride is None:stride=k-1
    n=3*h
    # edge=0 interior; bit 0 (1) is the low (high) cropped edge.
    cuts=(not edge&1) | ((not edge&2)<<(n-1))
    rim=(2 if edge&1 else 0)|((1<<(n-2)) if edge&2 else 0)
    states=Pool();base=states.intern((-1,tuple(range(n+1)),(0,)*n+(1,)))
    maps=Pool();maps.intern(frozenset());tables=Pool()
    @lru_cache(None)
    def physical(w):
        return tuple(cols(tuple(map(transpose,w)) if hor else w))
    @lru_cache(None)
    def push(s,w,rev,end,drop,add=0):
        z=states.items[s];ms=physical(w)
        for b in (range(2,-1,-1) if rev else range(3)):
            outside=end and not (ends&(2 if rev else 1))
            teeth=(1<<n)-1 if end and not outside and b==1 else rim
            if outside and not rev and b==1:teeth|=rootmask
            teeth|=add
            if b==1 and drop:teeth&=~omit
            open_side=outside and b==(2 if rev else 0)
            leaks=(1<<n)-1 if open_side else cuts
            if open_side and not rev:leaks=cuts|(leaks&~sealed)
            z=advance(z,ms[b],teeth,leaks)
            if z is None:return -1
        return states.intern(z)
    @lru_cache(None)
    def compatible(s,t):
        a,p,tag=states.items[s];b,q,other=states.items[t]
        N=n+1
        parent=[*p,*(N+c for c in q)]
        flags=[*tag,*other]
        def root(u):
            while u!=parent[u]:u=parent[u]
            return u
        def join(u,v):
            u=root(u);v=root(v)
            if u==v:return False
            parent[u]=v;flags[v]|=flags[u];return True
        assert join(n,n+N)
        for i in range(n):
            if ((a|b)>>i)&1 and not join(i,i+N):return False
        return all(parent[i]!=i or f!=2 for i,f in enumerate(flags))
    @lru_cache(None)
    def joint(ds):
        paths=None
        for d in ds:
            tab=defaultdict(list)
            for a,b,c,e in pool.items[d]:
                if hor:b,c=c,b
                tab[a,b].append((c,e))
            if paths is None:paths=[((a,c),(b,e)) for (a,b),ns in tab.items() for c,e in ns]
            else:paths=[((*w,c),(*y,e)) for w,y in paths for c,e in tab[w[-1],y[-1]]]
        return tables.intern(frozenset(paths))
    @lru_cache(None)
    def adj(t,rev):
        A=defaultdict(list)
        for w,y in tables.items[t]:
            if rev:w,y=y,w
            A[w].append(y)
        return A
    @lru_cache(None)
    def init(t,rev):
        return maps.intern(frozenset((w,v) for w in adj(t,rev)
            if (v:=push(base,w,rev,True,not hor and not rev and bool(omit),
                        2 if rootfrom is not None and (k-1 if rev else 0)>=rootfrom else 0))>=0))
    @lru_cache(None)
    def step(st,t,rev,drop,add):
        A=adj(t,rev)
        return maps.intern(frozenset((y,v) for w,s in maps.items[st]
                                     for y in A.get(w,()) if (v:=push(s,y,rev,False,drop,add))>=0))
    @lru_cache(None)
    def closure(st,ts,rev,add):
        seen={(w,s,0) for w,s in maps.items[st]};todo=list(seen)
        for w,s,j in todo:
            A=adj(ts[j],rev)
            for y in A.get(w,()):
                v=push(s,y,rev,False,False,add)
                n=y,v,(j+1)%len(ts)
                if v>=0 and n not in seen:seen.add(n);todo.append(n)
        return maps.intern(frozenset((w,s) for w,s,j in seen if j==0))
    @lru_cache(None)
    def group(st):
        m=defaultdict(list)
        for w,s in maps.items[st]:m[w].append(s)
        return m
    @lru_cache(None)
    def meet(l,t,r):
        L=group(l);R=group(r);out=[set() for _ in range(h-1)]
        for w,y in tables.items[t]:
            if not any(compatible(a,b) for a in L.get(w,()) for b in R.get(y,())):continue
            for i,p in enumerate(out):
                a,c=w[i:i+2];b,e=y[i:i+2]
                p.add((a,c,b,e) if hor else (a,b,c,e))
        return tuple(pool.intern(frozenset(p)) for p in out)
    def strip(grid,pos):
        off=pos*stride if hor else pos
        dj,di=(1,stride) if hor else (stride,1)
        ts=[joint(tuple(grid[off+j*dj+i*di] for i in range(h-1))) for j in range(k-1)]
        l=init(ts[0],False);ls=[]
        for j,t in enumerate(ts):
            add=2 if rootfrom is not None and j+1>=rootfrom else 0
            if j in along:l=closure(l,tuple(ts[j:j+block]),False,add)
            ls.append(l)
            if j<k-2:l=step(l,t,False,hor and bool(omit) and j+1==q,add)
            if not l:return False
        r=init(ts[-1],True)
        for j in reversed(range(k-1)):
            add=2 if rootfrom is not None and j>=rootfrom else 0
            if j-block+1 in along:r=closure(r,tuple(reversed(ts[j-block+1:j+1])),True,add)
            ids=meet(ls[j],ts[j],r)
            if not pool.items[ids[0]]:return False
            for i,v in enumerate(ids):
                if h==2 or not any(g<=pos+i<g+block and (pos<g or pos+h-2>=g+block) for g in across):
                    grid[off+j*dj+i*di]=v
            if j:r=step(r,ts[j],True,hor and bool(omit) and j==q,add)
        return True
    return strip

def check(axis,k,interval,hmax=3,data=None,q=None,gx=(),gy=(),block=1,rounds=1,inspect=None):
    it=iter(map(int,(data if data is not None else instance(axis,k,interval)).split()))
    assert next(it)==k;nt=next(it);pool=Pool();indices=[]
    for _ in range(nt):
        tab=frozenset(tuple(next(it) for _ in range(4)) for _ in range(next(it)))
        indices.append(pool.intern(tab))
    grid=[indices[x] for x in it];assert len(grid)==(k-1)**2
    for phase,h in enumerate(list(range(2,hmax+1))*rounds):
        if h==2:round_start=grid.copy()
        for turn in range(40):
            old=grid.copy()
            for hor in (True,False):
                fs={}
                along,across=(gx,gy) if hor else (gy,gx)
                for pos in (reversed(range(k-h+1)) if turn%2 else range(k-h+1)):
                    if h>3 and any(pos<g+block and pos+h-2>=g and not(g<=pos and pos+h-2<g+block)
                                   for g in across):continue
                    e=int(pos==0)+2*int(pos==k-h)
                    omit=0 if q is None else 2 if hor and pos==0 else (
                        1<<(3*(q-pos)+1) if not hor and pos<=q<pos+h else 0)
                    key=e,omit
                    if key not in fs:fs[key]=checker(k,h,hor,e,pool,q,omit,along,across,block)
                    if not fs[key](grid,pos):
                        print('independent EMPTY',axis,k,interval,h,turn,hor,pos,flush=True);return True
            if old==grid:break
        if h==hmax and round_start==grid:
            if inspect is not None:inspect(pool,grid)
            print('independent OPEN joint fixed point',axis,k,interval);return False
    if rounds>1:raise ValueError('no verified joint fixed point')
    print('independent OPEN',axis,k,interval);return False
if __name__=='__main__':
    import sys
    a,k=map(int,sys.argv[1:3]);lo,hi=map(int,sys.argv[3].split(':'))
    check(a,k,(lo,hi))
