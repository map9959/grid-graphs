"""Uniform component debit from freely choosing a marked sink in each tree."""
from itertools import combinations, product
from functools import lru_cache
from .diagonal_score import DIR, MASKS, Q, count, data
import sys

def run(n):
    assert n in (55,58) and '--deep' in sys.argv
    k=n//3
    pos,patch,star,sc,_=data(n,3*k*k+(32*k-7)//6)
    kinds=set()
    buckets=set()
    for i,j in product(range(n),repeat=2):
        z=pos(i,j,0);buckets.add(z[0])
        if (i,j)==(0,0):continue
        ds=tuple(s for s,(x,y) in enumerate(DIR) if 0<=i+x<n and 0<=j+y<n)
        kinds.add((z,ds,len(ds)==2))
    # Completeness in every size n+6t, from the exact bucket polynomials.
    coeff=list(zip(*(count(n,8,9,pt) for pt in buckets)))
    assert list(map(sum,coeff))==[n*n,12*n+36,72]
    marked=[];corner=[]
    for z,ds,extra in kinds:
        tab=star(z,ds,extra)[-1]
        for h in range(1<<len(ds)):
            if any(h>>a&h>>b&1 and (ds[a]-ds[b])%2
                   for a,b in combinations(range(len(ds)),2)):continue
            marked.append(Q(tab[2*h+1],sc))
            if extra:corner.extend(Q(v,sc) for v in tab[2*h:2*h+2])
    ans=min(marked),min(corner)
    assert ans==((Q(1,3) if n==55 else Q(1055,4953)),Q(5,6))
    print(n,'+6t: marked sink outside NW costs at least',ans[0],
          '; any additional corner sink costs at least',ans[1])
    if '--neighborhood' in sys.argv:
        @lru_cache(None)
        def table(z,ds):
            costs=star(z,ds,len(ds)==2)[-1];out={}
            for h in range(1<<len(ds)):
                if any(h>>a&h>>b&1 and (ds[a]-ds[b])%2
                       for a,b in combinations(range(len(ds)),2)):continue
                for f in (0,1):
                    for known in range(1<<len(ds)):
                        key=f,known,h&known
                        out[key]=min(out.get(key,costs[2*h+f]),costs[2*h+f])
            return out
        seen=set();best=None
        for i,j in product(range(n),repeat=2):
            block=(min(max(i-1,0),n-3),min(max(j-1,0),n-3))
            sites=[(i,j)]+[(i+x,j+y) for x,y in DIR if 0<=i+x<n and 0<=j+y<n]
            if (0,0) in sites:continue
            key=[pos(*block,1)]
            for x,y in sites:
                ds=tuple(s for s,(a,b) in enumerate(DIR) if 0<=x+a<n and 0<=y+b<n)
                key.append((pos(x,y,0),ds,x-block[0],y-block[1]))
            key=tuple(key)
            if key in seen:continue
            seen.add(key);terms=[]
            for z,ds,x,y in key[1:]:
                bits=[(h,3*(x+DIR[s][0])+y+DIR[s][1]) for h,s in enumerate(ds)
                      if 0<=x+DIR[s][0]<3 and 0<=y+DIR[s][1]<3]
                terms.append((3*x+y,table(z,ds),bits,sum(1<<h for h,_ in bits)))
            charges=patch(key[0])
            for m in MASKS:
                if not m>>terms[0][0]&1:continue
                costs=[t.get((m>>v&1,mask,sum((m>>b&1)<<h for h,b in bits)),None)
                       for v,t,bits,mask in terms]
                if None not in costs:
                    val=charges[m]+max(costs)
                    if best is None or val<best:best=val;where=(i,j,m)
        print('one patch plus best sink in marked closed neighborhood',Q(best,sc),where)

if __name__=='__main__':
    for n in (55,58):run(n)
