"""A full left-to-right rooted forest for every three-row crop strip."""
from collections import Counter,defaultdict
from .wired_strip_flow import advance,model,solve,count,trans,SYM,MASKS

def span(ns,A,n,d,w):
    S=n-2
    def axis(x,s,q):return x if x<q else 2*q+3+x-s if x>=s-q else q+(x-q)%3
    def key(i,j):
        l=d+3;cl=lambda z:max(-w-5,min(w+5,z))
        return axis(i,S,l),axis(j,S,l),cl(i-j),cl(i+j+1-S)
    def new(edge):
        x='x'+str(len(ns));ns['span',edge]=x;return x
    adj=defaultdict(Counter);marg=defaultdict(Counter);seen=set();positions={}
    multiplicity=Counter(axis(i,S,2) for i in range(S))
    initial=(-1,-1,(0,1,2,3))
    for i in range(S):
        g=axis(i,S,2);states={initial}
        for j in range(n):
            u,v=axis(j,n,3),axis(j+1,n,3);nxt=set()
            if j>=2:
                k=key(i,j-2);tag=g,u,v
                if k not in positions:
                    positions[k]=tag
                    pts=[key(*trans(i,j-2,S,s)) for s in range(8)]
                    for mask in MASKS:
                        x=ns.get(('p',min(zip(pts,SYM[mask]))))
                        if x:marg[tag,mask][x]-=1
                else:assert positions[k]==tag
            for st in states:
                for b in range(8):
                    z=advance(3,st,b,j in (0,n-1),i==0,i==S-1)
                    if z is None:continue
                    nxt.add(z);e=(g,u,v,st,b)
                    if e in seen:continue
                    seen.add(e);x=new(e)
                    adj[g,u,st][x]+=1
                    if j<n-1:adj[g,v,z][x]-=1
                    if j>=2:
                        mask=sum((col>>r&1)<<(3*r+c) for c,col in enumerate((*st[:2],b)) for r in range(3))
                        marg[(g,u,v),mask][x]+=1
            states=nxt
    rhs=[]
    for k,c in adj.items():
        g,u,st=k;A.append((list(c.items()),'='));rhs.append(g if (u,st)==(0,initial) else None)
    for c in marg.values():A.append((list(c.items()),'='));rhs.append(None)
    return rhs

def test(base,d,w,sizes):
    ns,A,keys,obj=model(base,d,w)
    rhs2=span(ns,A,base,d,w)
    print('span flow:',len(ns),'columns',len(rhs2),'new rows',flush=True)
    for n in sizes:
        assert n>=base and (n-base)%6==0
        mult=Counter(x if x<2 else 7+x-(n-2) if x>=n-4 else 2+(x-2)%3 for x in range(n-2))
        rhs=[count(n-2*(k[0]=='p'),d+4-(k[0]=='p'),w+5,k[1][0])[0] if k else 0 for k in keys]
        rhs.extend(mult[g] if g is not None else 0 for g in rhs2)
        v,_,_=solve(A,rhs,obj,ns,interior=True)
        print(n,'deficit',n*n/3-v,flush=True)
if __name__=='__main__':
    import sys
    b,d,w,*ns=map(int,sys.argv[1:]);test(b,d,w,ns)
