"""Exact checks of a compact two-axis error witness on the complete side-103 collar."""
from base64 import b85encode,b85decode
from pathlib import Path
from itertools import product
from fractions import Fraction as Q
import zlib
import sys
from .diagonal_score import data,DIR
from .repair_defect_budget import check_errors,charge

path=Path(__file__).with_name('repair_collar103.b85')

def domain(n,depth):return {(i,j) for i,j in product(range(n),repeat=2) if min(i,j,n-1-i,n-1-j)<depth}

def save(sol):
    raw=bytes(int(m)+2*(o+1) for _,(m,o) in sorted(sol.items()))
    path.write_bytes(b85encode(zlib.compress(raw,9))+b'\n')

def load():
    D=sorted(domain(103,12));raw=zlib.decompress(b85decode(path.read_bytes().strip()))
    assert len(raw)==len(D) and max(raw)<10
    return {v:(int(c&1),(c>>1)-1) for v,c in zip(D,raw)}

def audit(sol,tables):
    n=103;D=set(sol);p={u:u for u in D}
    def rt(u):
        while p[u]!=u:p[u]=p[p[u]];u=p[u]
        return u
    edges=0;X=list(range(1,n*n+1));ids={('a',u,s):1+n*n+4*u+s for u in range(n*n) for s in range(4)}
    truth=set()
    assert sol[0,0][1]==-1
    for (i,j),(m,out) in sol.items():
        u=i*n+j
        if m:truth.add(X[u])
        if out>=0:
            a,b=DIR[out];assert 0<=i+a<n and 0<=j+b<n
            truth.add(ids['a',u,out])
        for s,(a,b) in enumerate(DIR[:2]):
            v=i+a,j+b
            if v not in D:continue
            g,o=sol[v]
            assert int(out==s)+int(o==s+2)==int(bool(m or g))
            if m or g:
                x,y=rt((i,j)),rt(v);assert x!=y,'physical cycle'
                p[x]=y;edges+=1
    val,budget=charge(n,D,tables,X,ids,truth)
    errors=check_errors(n,lambda y,x:sol.get((y,x),(0,-1))[0])
    assert all(v[0]==81 for v in errors) and val<=budget
    print('sites',len(D),'forced edges',edges,'components',len(D)-edges,'frames',*[x[0] for x in errors])
    print('exact spent',val,'budget',budget,'remaining',budget-val,'at scale',tables[3])
    return val

def fringe(sol,tables):
    """Disjoint omitted terms, minimizing unknown neighbor bits independently."""
    n=103;pos,patch,star,_,_=tables;debits={}
    for (i,j),(m,out) in sol.items():
        ds=tuple(s for s,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n)
        vs=[(i+DIR[s][0],j+DIR[s][1]) for s in ds]
        if all(v in sol for v in vs):continue
        tab=star(pos(i,j,0),ds,False)[out]
        debits[i,j,0]=min(tab[m+sum(b<<(s+1) for s,b in enumerate(word))]
                           for word in product(*[(sol[v][0],) if v in sol else (0,1) for v in vs]))
    for i,j in product(range(n-2),repeat=2):
        vs=[(i+a,j+b) for a,b in product(range(3),repeat=2)]
        if not any(v in sol for v in vs) or all(v in sol for v in vs):continue
        tab=patch(pos(i,j,1));debits[i,j,1]=min(tab[sum(b<<s for s,b in enumerate(word))]
                   for word in product(*[(sol[v][0],) if v in sol else (0,1) for v in vs]))
    print('unavoidable fringe charge',sum(debits.values()),'positive anchors',sum(z>0 for z in debits.values()))
    if '--anchors' in sys.argv:print(sorted((k,v) for k,v in debits.items() if v))
    return sum(debits.values())

def best_orientation(sol,tables,exclude=None,quiet=False):
    """Minimum collar star bill over all rootings and exits. Mixed patches
    and incomplete stars minimize their missing marks independently."""
    n=103;pos,patch,star,sc,cap=tables;tabs={};adj={};exitcost={}
    for (i,j),(m,_) in sol.items():
        u=i,j;ds=tuple(s for s,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n)
        vs=[(i+DIR[s][0],j+DIR[s][1]) for s in ds]
        tab=star(pos(i,j,0),ds,len(ds)==2 and u!=(0,0))
        masks=[m+sum(bit<<(s+1) for s,bit in enumerate(word)) for word in
               product(*[(sol[v][0],) if v in sol else (0,1) for v in vs])]
        tabs[u]={s:min(tab[s][z] for z in masks) for s in (-1,*ds)}
        if exclude is not None and (not all(v in sol for v in vs) or u in exclude and all(v in exclude for v in vs)):
            tabs[u]=dict.fromkeys(tabs[u],0)
        adj[u]=[(v,s) for s,v in zip(ds,vs) if v in sol and (m or sol[v][0])]
        exitcost[u]=min(tabs[u][s] for s in [-1,*[s for s,v in zip(ds,vs) if v not in sol]])
    total=0;seen=set()
    for src in sorted(sol):
        if src in seen:continue
        order=[src];parents={src:None};seen.add(src);base=0
        for u in order:
            for v,s in adj[u]:
                if v==parents[u]:continue
                assert v not in seen;seen.add(v);parents[v]=u;order.append(v)
                base+=tabs[v][(s+2)%4]
        offs={src:base}
        for u in order:
            for v,s in adj[u]:
                if v!=parents[u]:offs[v]=offs[u]+tabs[u][s]-tabs[v][(s+2)%4]
        total+=base+tabs[src][-1] if src==(0,0) else min(offs[v]+exitcost[v] for v in order)
    patchcost=0
    origins=product(range(n-2),repeat=2) if exclude is None else ((i,j) for i,j in sol if i<n-2 and j<n-2)
    for i,j in origins:
        vs=[(i+a,j+b) for a,b in product(range(3),repeat=2)]
        if exclude is not None and (not all(v in sol for v in vs) or all(v in exclude for v in vs)):continue
        if any(v in sol for v in vs):
            tab=patch(pos(i,j,1));patchcost+=min(tab[sum(b<<s for s,b in enumerate(word))]
                   for word in product(*[(sol[v][0],) if v in sol else (0,1) for v in vs]))
    if not quiet:print('all-rootings lower: stars',total,'patches',patchcost,'sum',total+patchcost,'budget',cap)
    return total+patchcost

if __name__=='__main__':
    assert '--deep' in sys.argv
    sol=load();tables=data(103,3647);audit(sol,tables);fringe(sol,tables);best_orientation(sol,tables)
