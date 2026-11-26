"""Bent oblique interfaces: two independent directed costs, one loss budget."""
from collections import Counter,defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
import subprocess
from .period_nine import budgets
from .oblique_rails import cut,arbitrary_arms


def compact(d):
    v,h,l,ms,_=cut(d)
    hist=sum(((m>>(2*j+1-z%2))&1)<<(3*z+j) for z,m in enumerate(ms) for j in range(3))
    return v,h,l,hist


def setup(res):
    rows=arbitrary_arms([q for q in budgets(6,res) if
                         all(q[1][r,c]==q[1][r,(c+6)%12] for r,c in q[1])],res)
    last=8+6*res
    st={}
    for i,d,_ in rows:
        for right in (False,True):
            def get(r,c):
                x,y=d[c,(last-r if right else r)%12]
                return (-y if right else y),x
            st[right,i]=compact({(r,c):get(r,c) for r,c in d})
    return rows,st


def solve_pairs(queries):
    by_start=defaultdict(dict)
    for (a,b),budget in queries.items():by_start[a][b]=budget
    result={}
    binary=Path(__file__).resolve().parents[2]/"target/release/oblique_cost"
    for a,ends in by_start.items():
        limit=max(ends.values())
        data=[limit,*a,*(w for b in ends for w in b)]
        proc=subprocess.run([binary],input=' '.join(map(str,data)),capture_output=True,text=True,check=True)
        _,*ds=map(int,proc.stdout.split())
        for b,d in zip(ends,ds,strict=True):result[a,b]=min(d,limit+1)
    return result


@lru_cache(None)
def row_out(occ):
    """Match any free sites to tangent neighbors or to the next normal row."""
    allbits=4095
    def rec(free,out):
        if not free:
            yield out
            return
        bit=free&-free
        yield from rec(free^bit,out|bit)
        for adj in ((bit>>1)|((bit&1)<<11),((bit<<1)&allbits)|(bit>>11)):
            if free&adj:yield from rec(free^bit^adj,out)
    return set(rec(allbits^occ,0))


def stem_state(d):
    inc=sum(1<<j for j in range(12) if d[j,0]==(0,-1))
    mid=sum(1<<j for j in range(0,12,2) if d[j,11][0]==0)
    return inc,mid,0


@lru_cache(None)
def stem_zero(start):
    from collections import deque
    seen={start};q=deque([start])
    while q:
        occ,prev,ph=q.popleft()
        for out in row_out(occ):
            tan=4095^(occ|out)
            for end in row_out(out):
                mid=(out|end)&1365
                if all(sum((m>>(i%12))&1 for m,i in ((prev,j),(mid,j),(tan,j-1),(tan,j+1)))
                       in (1,4) for j in range(0,12,2)):
                    st=end,mid,(ph+1)%6
                    if st not in seen:
                        seen.add(st);q.append(st)
    return seen


def census():
    cases=[];queries={};axis=[]
    for res in (0,1):
        rows,st=setup(res)
        triples=[]
        for (l,_,a),(m,_,b),(r,_,c) in product(rows,repeat=3):
            arm=2*(a[3]+b[0]+c[1])+a[2]+c[2]
            budget=(12-arm)//2
            if budget<0:continue
            left=st[False,l],st[False,m]
            right=st[True,r],st[True,m]
            triples.append(((l,m,r),budget,left,right))
            for key in (left,right):queries[key]=max(budget,queries.get(key,-1))
        cases.append(triples)
        straight=[]
        for x2 in (0,1,2):
            for (l,d,a),(r,e,c) in product(rows,repeat=2):
                budget=(12-2*(a[3]+c[1])-x2*(a[0]+a[2])-(2-x2)*(c[0]+c[2]))//2
                if budget<0:continue
                assert budget==0
                straight.append((x2,l,r,stem_state(e) in stem_zero(stem_state(d))))
        axis.append(straight)
    # Start cheaply. Never treat a threshold failure as an exact distance.
    lower=solve_pairs({k:min(b,2) for k,b in queries.items()})
    print("distinct directed seam queries",len(queries),"thresholded costs",
          dict(sorted(Counter(lower.values()).items())),flush=True)
    for triples in cases:
        rem=[t for t in triples if lower[t[2]]+lower[t[3]]<=t[1]]
        print("triples",len(triples),"budget counts",dict(Counter(t[1] for t in triples)),
              "after threshold two",len(rem),flush=True)
    todo={}
    for triples in cases:
        for _,b,l,r in triples:
            if lower[l]+lower[r]>b:continue
            for key,other in ((l,r),(r,l)):
                if lower[key]==3 and b-lower[other]>=3:
                    todo[key]=max(todo.get(key,0),b-lower[other])
    lower.update(solve_pairs(todo))
    for res,triples in enumerate(cases):
        rem=[(ids,b,lower[l],lower[r]) for ids,b,l,r in triples if lower[l]+lower[r]<=b]
        print("residue",res,"surviving joins",len(rem),rem[:6],flush=True)
        print("axis budget-zero pairs by x=0,1/2,1",dict(Counter(x/2 for x,i,j,hit in axis[res])),
              "axis hits",sum(hit for x,i,j,hit in axis[res]),"all-Y-position exclusion",
              not rem and not any(hit for x,i,j,hit in axis[res]),flush=True)
    return cases,lower


if __name__=='__main__':census()
