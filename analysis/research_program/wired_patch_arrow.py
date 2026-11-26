"""Condition the directions of interior arrows on the physical mask of a patch."""
from collections import Counter,defaultdict
from functools import lru_cache
from .patch_square import P,DIR,EDGES,SYM,MASKS,trans,local
from .square_current import states
from .wired_crop_sector import solve,model,count
import sys

@lru_cache(None)
def routing(m,teeth):
    adj=[[] for _ in P]
    for a,b in EDGES:
        if (m>>a|m>>b)&1:adj[a].append(b);adj[b].append(a)
    rem=set(range(9));out=[]
    while rem:
        v=min(rem);part=[v];rem.remove(v)
        for x in part:
            for y in adj[x]:
                if y in rem:rem.remove(y);part.append(y)
        roots=[x for x in part if teeth>>x&1]
        if len(roots)>1:return
        opts=[]
        for root in roots or part:
            order=[root];ds={root:-1}
            for x in order:
                for y in adj[x]:
                    if y in ds:continue
                    ds[y]=DIR.index(tuple(a-b for a,b in zip(P[x],P[y])));order.append(y)
            opts.append(ds)
        out.append(opts)
    return out

def lift(ns,A,n,d,w,band):
    def key(i,j,S,fine=True):
        h=d+4-int(S!=n) if fine else d;clip=w+5 if fine else w
        ax=lambda x:x if x<h else 2*h+3+x-S if x>=S-h else h+(x-h)%3
        cl=lambda x:max(-clip,min(clip,x))
        return ax(i),ax(j),cl(i-j),cl(i+j+1-S)
    def imgs(i,j,S):return [key(*trans(i,j,S,g),S) for g in range(8)]
    @lru_cache(None)
    def stars(i,j):
        ps=imgs(i,j,n);ds=[k for k,(u,v) in enumerate(DIR) if 0<=i+u<n and 0<=j+v<n];tab=[]
        for f,sg in states(ds):
            nb=[sg[s][int(s<2)] if s in ds else 9 for s in range(4)]
            out=next((s for s,z in sg.items() if z[2]==(1 if s<2 else -1)),-1)
            opts=[]
            for g,p in enumerate(ps):
                rot=lambda s:((2-s if g&4 else s)+g)%4;v=[9]*4
                for s in ds:v[rot(s)]=nb[s]
                opts.append((p,f,tuple(v),rot(out) if out>=0 else -1))
            x=ns.get(('s',min(opts)))
            if x:tab.append((x,f,nb,out))
        return tab
    S=n-2;seen=set();eq=defaultdict(Counter);starpos=set();norm=[]
    for i in range(S):
        for j in range(S):
            if i>=band:continue
            ps=imgs(i,j,S);p=ps[0]
            co=key(i,j,S,False)
            teeth=sum(1<<v for v,(u,b) in enumerate(P) if min(i+u,j+b,n-1-i-u,n-1-j-b)==0)
            for v,(u,b) in enumerate(P):
                sk=key(i+u,j+b,n);tag=co,v,sk
                if tag in starpos:continue
                starpos.add(tag)
                dirs=[s for s,(a,c) in enumerate(DIR) if 0<=u+a<3 and 0<=b+c<3]
                for x,f,nb,o in stars(i+u,j+b):
                    # A star fine bucket can straddle a chosen strip end
                    # only if that end was outside the exact boundary labels.
                    eq[co,v,(f,)+tuple(nb[s] for s in dirs),o if o in dirs else -1][x]-=1
            if p in seen:continue
            seen.add(p)
            for m in MASKS:
                x=ns.get(('p',min(zip(ps,SYM[m]))))
                if x is None:continue
                routes=routing(m,m&teeth)
                if routes is None:norm.append(([(x,1)],'='));continue
                for a,opts in enumerate(routes):
                    ys=[]
                    for k,table in enumerate(opts):
                        y=x
                        if len(opts)>1:
                            y='x'+str(len(ns));ns['route',p,m,a,k]=y;ys.append(y)
                        for v,o in table.items():eq[co,v,local(m,v),o][y]+=1
                    if ys:norm.append(([(y,1) for y in ys]+[(x,-1)],'='))
    A.extend(norm);A.extend((list(c.items()),'=') for c in eq.values())

def test(n,d,w,band,sizes):
    assert 1<=band<=d
    ns,A,keys,obj=model(n,d,w);k=len(A)
    lift(ns,A,n,d,w,band)
    print('patch exits',len(ns),'columns',len(A)-k,'new rows',flush=True)
    for N in sizes:
        assert N>=n and (N-n)%6==0
        rhs=[count(N-2*(k[0]=='p'),d+4-(k[0]=='p'),w+5,k[1][0])[0] if k else 0 for k in keys]
        v,_,_=solve(A,rhs+[0]*(len(A)-len(rhs)),obj,ns,interior=True);print(N,'deficit',N*N/3-v,flush=True)
if __name__=='__main__':
    n,d,w,b,*N=map(int,sys.argv[1:]);test(n,d,w,b,N)
