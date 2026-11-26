"""Couple the entire NW-SE diagonal band, using its moving physical frontier."""
from functools import lru_cache
from collections import Counter,defaultdict
from .wired_strip_flow import model,solve,count,trans,SYM,MASKS
from .patch_square import relaxation
import sys

@lru_cache(None)
def move(h,st,v,wire):
    a,b,part=st
    if b>=0 and v&(b|b>>2):return
    q=list(part)+list(range(h+1,2*h+1))
    def rt(i):
        while q[i]!=i:i=q[i]
        return i
    def join(i,j):
        i,j=rt(i),rt(j);q[i]=j;return i!=j
    for i in range(h):
        z=h+1+i
        if b>=0 and i<h-1 and ((b>>(i+1)|v>>i)&1) and not join(i+1,z):return
        if i and v>>(i-1)&3 and not join(z-1,z):return
        if v&wire&(1<<i) and not join(z,h):return
    out=[rt(h+1+i) for i in range(h)]+[rt(h)]
    return b&~3,v,tuple(out.index(i) for i in out)

def band(ns,A,n,d,w,h,wire):
    lo=-(h//2);S=n-2
    def ax(i,s,l):return i if i<l else 2*l+3+i-s if i>=s-l else l+(i-l)%3
    def key(i,j):
        cl=lambda z:max(-w-5,min(w+5,z))
        return ax(i,S,d+3),ax(j,S,d+3),cl(i-j),cl(i+j+1-S)
    adj=defaultdict(Counter);patch=defaultdict(Counter);positions={};seen=set()
    initial=(-1,-1,tuple(range(h+1)));states={initial};l=h//2+2
    assert max(abs(lo+2),abs(lo+h-3))<w+5
    for j in range(n):
        u,v=ax(j,n,l),ax(j+1,n,l)
        rows=[j+lo+r for r in range(h)]
        avail=sum((0<=y<n)<<r for r,y in enumerate(rows))
        wired=sum((0<=y<n and (y in (0,n-1) or j in (0,n-1)))<<r for r,y in enumerate(rows)) if wire else 0
        tags=[]
        for r in range(h-4):
            y=rows[r]
            if j<2 or not 0<=y<S:continue
            k=key(y,j-2);tag=u,v,r;tags.append((r,tag))
            if k in positions:assert positions[k]==tag;continue
            positions[k]=tag;pts=[key(*trans(y,j-2,S,g)) for g in range(8)]
            for m in MASKS:
                x=ns.get(('p',min(zip(pts,SYM[m]))))
                if x:patch[tag,m][x]-=1
        nxt=set()
        for st in states:
            for b in range(1<<h):
                if b&~avail:continue
                z=move(h,st,b,wired)
                if z is None:continue
                nxt.add(z);e=u,v,st,b
                if e in seen:continue
                seen.add(e);x='x'+str(len(ns));ns['diagflow',e]=x
                adj[u,st][x]+=1
                if j<n-1:adj[v,z][x]-=1
                for r,tag in tags:
                    m=sum((col>>(r+2-c+i)&1)<<(3*i+c) for c,col in enumerate((*st[:2],b)) for i in range(3))
                    patch[tag,m][x]+=1
        states=nxt
    init=(0,initial)
    add=[(list(c.items()),'=') for c in patch.values()]
    add.extend((list(c.items()),'=') for k,c in adj.items() if k!=init)
    add.append((list(adj[init].items()),'='));A.extend(add);return len(add)

def test(base,d,w,h,sizes):
    wired='--wired' in sys.argv
    if wired:ns,A,keys,obj=model(base,d,w);rhs0=[0]*len(keys)
    else:
        ns,rs,obj=relaxation(base,d+4,pooled=d,period=3,diagonal=w);inv={x:k for k,x in ns.items()}
        A=[];keys=[];rhs0=[]
        for cs,op,b in rs:
            A.append((cs,op));keys.append(inv[cs[0][0]] if b and op=='=' else None);rhs0.append(b)
    m=band(ns,A,base,d,w,h,wired);print('diagonal span',h,len(ns),m,'new rows',flush=True)
    for n in sizes:
        assert n>=base and (n-base)%6==0
        rhs=[count(n-2*(k[0]=='p'),d+4-(k[0]=='p'),w+5,k[1][0])[0] if k else b for b,k in zip(rhs0,keys)]
        v,_,_=solve(A,rhs+[0]*(m-1)+[1],obj,ns,interior=True)
        print(n,'score',v,'delta against base',v-(n*n/3 if wired else 3*(n//3)**2+16*(n//3)/3-7/6),flush=True)
if __name__=='__main__':
    b,d,w,h,*n=map(int,[s for s in sys.argv[1:] if not s.startswith('--')]);test(b,d,w,h,n)
