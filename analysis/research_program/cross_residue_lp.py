"""Add both neighbor-square inequalities to the unrestricted sector LP."""
from collections import Counter,defaultdict
from .patch_square import MASKS,SYM,trans,relaxation
from .side28_score import solve
from .chart_counts import count

def terms(ns,n,d,w):
    # Assign every occurrence to one physical 3x3 window, then sum its
    # local coefficient once per fine position type (mass already counted).
    events=defaultdict(list);S=n-2;h=d+3
    def event(k,sites):
        i=min(S-1,min(i for i,j in sites));j=min(S-1,min(j for i,j in sites))
        events[i,j].append((k,tuple(3*(y-i)+x-j for y,x in sites)))
    for i in range(n):
        for j in range(n):
            depth=min(i,j,n-1-i,n-1-j)
            if depth<2:event('ext',[(i,j)])
            if i in (2,n-3) and j in (2,n-3):event('corner',[(i,j)])
    for g in range(4):
        def at(y,x):return trans(y,x,n,g)
        for x in range(n-1):event('gap',[at(0,x),at(0,x+1)])
        for x in range(2,n-2):
            event('normal',[at(2,x),at(3,x)])
            if x not in (2,n-3):
                event('tooth',[at(2,x)]);event('unback',[at(2,x),at(0,x)])
    def key(i,j):
        ax=lambda a:a if a<h else 2*h+3+a-S if a>=S-h else h+(a-h)%3
        cl=lambda a:max(-w-5,min(w+5,a))
        return ax(i),ax(j),cl(i-j),cl(i+j+1-S)
    seen={};cs=defaultdict(Counter)
    for i in range(S):
        for j in range(S):
            p=key(i,j);sig=tuple(sorted(events[i,j]))
            if p in seen:assert seen[p]==sig;continue
            seen[p]=sig
            if not sig:continue
            pts=[key(*trans(i,j,S,g)) for g in range(8)]
            for mask in MASKS:
                x=ns['p',min(zip(pts,SYM[mask]))]
                for k,inds in sig:
                    a=tuple(mask>>b&1 for b in inds)
                    cs[k][x]+=int(not any(a) if k=='gap' else a==(1,0) if k=='unback' else any(a))
    return cs

def test(base,n,d,w):
    ns,rows,obj=relaxation(base,d+4,pooled=d,period=3,diagonal=w)
    A=[];b=[];inv={x:v for v,x in ns.items()}
    for cs,op,r in rows:
        if r and op=='=':
            k,atom=inv[cs[0][0]];p=int(k=='p');r=count(n-2*p,d+4-p,w+5,atom[0])[0]
        A.append((cs,op));b.append(r)
    c=terms(ns,base,d,w)
    k=n//3;near=3*k*k+3*k-2;far=3*k*k+7*k-(k-5)//7-int(k%14==11)
    vals=[]
    for nm,weights,rhs in [
        ('near',{'ext':-2,'corner':-2,'unback':-2,'gap':-2,'normal':-1},2*(near-4*(n-1)+12)),
        ('far',{'ext':-2,'corner':-2,'unback':-3,'gap':-3,'tooth':1},2*(far-4*(n+1)+9)-3)]:
        row=Counter({x:2*z for x,z in obj.items()})
        for name,a in weights.items():
            for x,z in c[name].items():row[x]+=a*z
        vals.append((nm,row,rhs))
    def report():
        v,_,pr=solve(A,b,obj,ns,interior=True)
        print(n,'upper estimate',round(v,6),'exchange margins',[(nm,round((rhs-sum(z*pr[x] for x,z in row.items()))/2,6)) for nm,row,rhs in vals],flush=True)
    report()
    for nm,row,rhs in vals:A.append((list(row.items()),'<='));b.append(rhs)
    report()
if __name__=='__main__':
    import sys
    base,n=map(int,sys.argv[1:]);test(base,n,4,4)
