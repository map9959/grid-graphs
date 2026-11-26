"""Period-nine composition through an independently chosen saturated background."""
from collections import Counter
from itertools import product
from pathlib import Path
import subprocess

from .period_nine import backgrounds, pairs, state


def query(layouts, jobs):
    jobs=sorted(set(jobs))
    start=[state(d) for d in layouts]
    end=[state(d,True) for d in layouts]
    lines=[" ".join(map(str,[*start[i],*end[j],b,i,j])) for i,j,b in jobs]
    binary=Path(__file__).resolve().parents[2]/"target/release/diagonal_nine"
    result=subprocess.run([binary],input="\n".join(lines),text=True,capture_output=True,check=True)
    out={}
    for (i,j,b),line in zip(jobs,result.stdout.splitlines(),strict=True):
        u,v,c=map(int,line.split())
        assert (u,v)==(i,j)
        # The median-slice search is complete up to the requested budget.
        out[i,j,b]=min(c,b+1)
    return out


def census():
    layouts=list(backgrounds())
    ids=[i for i,d in enumerate(layouts) if state(d)[0].bit_count()==9]
    low=query(layouts,((i,j,1) for i,j in product(ids,repeat=2)))
    print("balanced middle layouts:",len(ids),"all ordered distances (2 means >=2):",
          dict(Counter(low.values())),flush=True)
    cases=[pairs(9,r) for r in range(3)]
    jobs=set()
    cand=[]
    for _,pairs_ in cases:
        triples=[]
        for i,j,b in pairs_:
            for m in ids:
                left,right=low[i,m,1],low[m,j,1]
                if left+right<=b:
                    triples.append((i,m,j,b))
                    jobs.update(((i,m,b-right),(m,j,b-left)))
        cand.append(triples)
    jobs.update(((14,26,2),(26,50,2)))
    dist=query(layouts,jobs)
    assert dist[14,26,2]==dist[26,50,2]==2
    print("positive composition control: 14 -> 26 -> 50; shared cost 2+2=4")
    for r,((rows,ps),triples) in enumerate(zip(cases,cand)):
        passed=[]
        for i,m,j,b in triples:
            x=dist[i,m,b-low[m,j,1]]
            y=dist[m,j,b-low[i,m,1]]
            if x+y<=b:
                passed.append((i,m,j,b))
        genuine=sum(i!=m and j!=m for i,m,j,_ in triples)
        print("k mod 3",(1+r)%3,"outer pairs",len(ps),"triples",len(ids)*len(ps),
              "genuine after cost-one test",genuine,"target survivors",len(passed),flush=True)
        if passed:
            print("surviving witnesses",passed[:5])
        # Macroscopic offsets -n/2,+n/2: relaxed arm costs plus two independently
        # optimized joins. Two side-nine steps give a shared budget of 18.
        # Each half-interface grows by one period over these two steps.
        c=[x for _,_,x in rows]
        tr=[sum(x[:2]) for x in c]
        bl=[sum(x[2:]) for x in c]
        assert min(tr[i]+bl[i] for i in ids)==18
        assert all(min(tr[i],bl[i])>=1000 for i in range(len(rows)) if i not in ids)
        best=best_genuine=10**6; contenders=[]
        for m in ids:
            l=[(tr[i]+bl[m]+low[i,m,1],i) for i in ids]
            h=[(tr[m]+bl[j]+low[m,j,1],j) for j in ids]
            v=min(l)[0]+min(h)[0]
            best=min(best,v)
            best_genuine=min(best_genuine,min(x for x,i in l if i!=m)+min(x for x,j in h if j!=m))
            for lc,i in l:
                for hc,j in h:
                    if lc+hc<=18:
                        contenders.append((i,m,j,18-tr[i]-bl[m]-tr[m]-bl[j]))
        print("half-offset lower bound",best,"genuine lower bound",best_genuine,
              "budget 18","triples remaining",len(contenders),flush=True)
        # Stronger bound: each of the two one-interface sums is >=10
        # if its individual target 9 is excluded. Use the computed two-leg
        # exclusion, which includes M equal to an endpoint, not a prior claim.
        if not passed:
            print("each composed top/right-to-bottom/left account costs >=10; budget 9")
    return low


if __name__=="__main__":
    census()
