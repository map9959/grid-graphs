"""All actual rim sites wired, charging the lost rank against the actual rim gaps."""
from functools import lru_cache
from collections import Counter,defaultdict
from .patch_square import relaxation,MASKS,SYM,trans
from .wired_crop_sector import count,solve
from .cross_residue_lp import terms

@lru_cache(None)
def step(h,s,v,side):
    a,b,part=s
    if b>=0 and b&(v<<1|v>>1):return
    q=[*part,*range(h+1,2*h+1)]
    def rt(i):
        while q[i]!=i:i=q[i]
        return i
    def join(i,j):
        i,j=rt(i),rt(j);q[i]=j;return int(i==j)
    lost=0
    for i in range(h):
        j=h+1+i
        if b>=0 and ((v|b)>>i&1):lost+=join(i,j)
        if not side and i and v>>(i-1)&3:lost+=join(j-1,j)
        if side:lost+=join(j,h)
    out=[rt(h+1+i) for i in range(h)]+[rt(h)]
    return (b,v,tuple(out.index(i) for i in out)),lost

def test(n,d,w,h,sizes):
    ns,rows,obj=relaxation(n,d+4,pooled=d,period=3,diagonal=w)
    gaps=terms(ns,n,d,w)['gap'];inv={x:k for k,x in ns.items()};A=[];rhs0=[];keys=[]
    for cs,op,b in rows:
        A.append((cs,op));keys.append(inv[cs[0][0]] if b and op=='=' else None);rhs0.append(b)
    S=n-2
    def ax(x,s,l):return x if x<l else 2*l+3+x-s if x>=s-l else l+(x-l)%3
    def key(i,j):
        cl=lambda z:max(-w-5,min(w+5,z))
        return ax(i,S,d+3),ax(j,S,d+3),cl(i-j),cl(i+j+1-S)
    adj=defaultdict(Counter);marg=defaultdict(Counter);cost=defaultdict(Counter);seen=set();pos={}
    ini=(-1,-1,tuple(range(h+1)));span=n-h+1
    for i in range(1,span-1):
        g=ax(i,span,2);states={ini}
        for j in range(n):
            u,v=ax(j,n,3),ax(j+1,n,3)
            if j>=2:
                for r in range(h-2):
                    k=key(i+r,j-2);tag=g,u,v,r
                    if (k,r) in pos:assert pos[k,r]==tag;continue
                    pos[k,r]=tag
                    pts=[key(*trans(i+r,j-2,S,s)) for s in range(8)]
                    for mask in MASKS:marg[tag,mask][ns['p',min(zip(pts,SYM[mask]))]]-=1
            nxt=set()
            for st in states:
                for b in range(1<<h):
                    z=step(h,st,b,j in (0,n-1))
                    if not z:continue
                    dest,lost=z;nxt.add(dest);e=g,u,v,st,b
                    if e in seen:continue
                    seen.add(e);x='x'+str(len(ns));ns['rr',e]=x
                    adj[g,u,st][x]+=1
                    if j<n-1:adj[g,v,dest][x]-=1
                    if lost:cost[g][x]+=lost
                    if j>=2:
                        for r in range(h-2):
                            mask=sum((col>>(r+t)&1)<<(3*t+c) for c,col in enumerate((*st[:2],b)) for t in range(3))
                            marg[(g,u,v,r),mask][x]+=1
            states=nxt
    mult=[]
    for (g,u,st),c in adj.items():
        A.append((list(c.items()),'='));mult.append(g if (u,st)==(0,ini) else None)
    for c in marg.values():A.append((list(c.items()),'='));mult.append(None)
    # Each residue mod h gives disjoint strips. When h=3 the bucket g
    # determines that residue, so the three budgets can be kept separate.
    bills=[]
    for r in range(3 if h==3 else 1):
        cs=Counter();seen_g=set()
        for i in range(1,span-1):
            g=ax(i,span,2)
            if h==3 and i%3!=r or g in seen_g:continue
            seen_g.add(g);cs.update(cost[g])
        scale=1 if h==3 else h
        for x,z in gaps.items():cs[x]-=scale*z
        A.append((list(cs.items()),'<='));bills.append(-scale)
    print('wired rim rank',h,len(ns),len(A),'rows',flush=True)
    for N in sizes:
        assert N>=n and (N-n)%6==0
        rhs=[count(N-2*(k[0]=='p'),d+4-(k[0]=='p'),w+5,k[1][0])[0] if k else b for k,b in zip(keys,rhs0)]
        sp=N-h+1;ms=Counter(ax(i,sp,2) for i in range(1,sp-1))
        rhs.extend(ms[g] if g is not None else 0 for g in mult)
        score,_,p=solve(A,rhs+bills,obj,ns,interior=True)
        print(N,'real upper estimate',score,'gaps',sum(z*p[x] for x,z in gaps.items()),flush=True)
if __name__=='__main__':
    import sys
    n,h,*N=map(int,sys.argv[1:]);test(n,4,4,h,N)
