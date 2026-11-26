"""Every wired component carries one consistent side of origin (unrooted ones choose freely)."""
from collections import Counter,defaultdict
from .patch_square import DIR,P,MASKS,SYM,trans,local,EDGES
from .square_current import states
from .wired_crop_sector import model,solve,count

def lift(ns,A,n,d,w,patch=True):
    def key(i,j,S,fine):
        h=d+4-int(S!=n) if fine else d;clip=w+5 if fine else w
        ax=lambda x:x if x<h else 2*h+3+x-S if x>=S-h else h+(x-h)%3
        cl=lambda x:max(-clip,min(clip,x))
        return ax(i),ax(j),cl(i-j),cl(i+j+1-S)
    def pts(i,j,S):return [key(*trans(i,j,S,g),S,True) for g in range(8)]
    def rot(g,s):return ((2-s if g&4 else s)+g)%4 if s>=0 else -1
    def var(k):
        if k not in ns:ns[k]='x'+str(len(ns))
        return ns[k]
    norms={};edge=defaultdict(Counter);pr=defaultdict(Counter);seen=set()
    def norm(x,ys):
        cs=Counter(ys);cs[x]-=1
        norms[tuple(sorted(cs.items()))]=True
    for i in range(n):
        for j in range(n):
            pp=pts(i,j,n);p=pp[0]
            if p in seen:continue
            seen.add(p);ds=[s for s,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n]
            pc=key(i,j,n,False);tag=[]
            for s,(a,b) in enumerate(DIR):
                oc=key(i+a,j+b,n,False) if s in ds else None
                tag.append((pc,oc,s) if s<2 else (oc,pc,s-2))
            patch_keys=[]
            if patch:
                for t,(u,v) in enumerate(P):
                    y,x=i-u,j-v
                    if 0<=y<n-2 and 0<=x<n-2:
                        dirs=[s for s,(a,b) in enumerate(DIR) if 0<=u+a<3 and 0<=v+b<3]
                        patch_keys.append((key(y,x,n-2,False),t,dirs))
            for f,sg in states(ds):
                nb=[sg[s][int(s<2)] if s in ds else 9 for s in range(4)]
                out=next((s for s,z in sg.items() if z[2]==(1 if s<2 else -1)),-1)
                opts=[]
                for g,z in enumerate(pp):
                    v=[9]*4
                    for s in ds:v[rot(g,s)]=nb[s]
                    opts.append((z,f,tuple(v),rot(g,out)))
                x=ns.get(('s',min(opts)))
                if x is None:continue
                colors=[s for s in range(4) if s not in ds] if f and len(ds)<4 else range(4)
                ys=[]
                for c in colors:
                    y=var(('side-s',min((*a,rot(g,c)) for g,a in enumerate(opts))));ys.append(y)
                    for s in ds:
                        if f or nb[s]:edge[tag[s],sg[s],c][y]+=1 if s<2 else -1
                    for q,t,dirs in patch_keys:pr[q,pc,t,(f,)+tuple(nb[s] for s in dirs),c][y]-=1
                norm(x,ys)
    seen.clear()
    if patch:
        S=n-2
        for i in range(S):
            for j in range(S):
                pp=pts(i,j,S);p=pp[0]
                if p in seen:continue
                seen.add(p);q=key(i,j,S,False)
                for m in MASKS:
                    x=ns.get(('p',min(zip(pp,SYM[m]))))
                    if x is None:continue
                    adj=[[] for _ in P]
                    for a,b in EDGES:
                        if (m>>a|m>>b)&1:adj[a].append(b);adj[b].append(a)
                    rem=set(range(9))
                    while rem:
                        part=[min(rem)];rem.remove(part[0])
                        for a in part:
                            for b in adj[a]:
                                if b in rem:rem.remove(b);part.append(b)
                        colors=set(range(4))
                        for t in part:
                            if not m>>t&1:continue
                            u,v=P[t];sides={s for s,(a,b) in enumerate(DIR) if not(0<=i+u+a<n and 0<=j+v+b<n)}
                            if sides:colors&=sides
                        bits=[min(3*a+b for t in part for a,b in [trans(*P[t],3,g)]) for g in range(8)]
                        ys=[]
                        for c in colors:
                            y=var(('side-p',min((p,z,tt,rot(g,c)) for g,(p,z,tt) in enumerate(zip(pp,SYM[m],bits)))));ys.append(y)
                            for t in part:
                                u,v=P[t];pr[q,key(i+u,j+v,n,False),t,local(m,t),c][y]+=1
                        norm(x,ys)
    unique={tuple(sorted((x,z) for x,z in cs.items() if z)) for bucket in (edge,pr) for cs in bucket.values()}
    A.extend((list(cs),'=') for cs in [*norms,*unique] if cs)

def test(n,d,w,sizes,patch):
    ns,A,keys,obj=model(n,d,w)
    lift(ns,A,n,d,w,patch);print('side colors',len(ns),'atoms',len(A),'rows',flush=True)
    for N in sizes:
        assert N>=n and (N-n)%6==0
        b=[count(N-2*(k[0]=='p'),d+4-(k[0]=='p'),w+5,k[1][0])[0] if k else 0 for k in keys]
        v,_,_=solve(A,b+[0]*(len(A)-len(b)),obj,ns,interior=True);print(N,'deficit',N*N/3-v,flush=True)
if __name__=='__main__':
    import sys
    n,d,w,*N=map(int,[s for s in sys.argv[1:] if not s.startswith('--')])
    test(n,d,w,N,'--patch' in sys.argv)
