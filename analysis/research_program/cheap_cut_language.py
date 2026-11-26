"""Determinize the billed strip in aligned triples of output bits."""
from functools import lru_cache
from itertools import product
from .cheap_cross_section import edge

def language(budget):
    start=((-1,tuple(range(4)),False,0),)
    @lru_cache(None)
    def bit(state,b):
        best={}
        for old,part,pending,paid in state:
            prev=max(old,0)
            for v in range(16):
                if bool(v&4)!=b:continue
                z=edge(old,part,v)
                if z is None:continue
                cost=paid+(v&14&~(v<<1)&~prev).bit_count()+int(pending and not b)
                key=v,z,not(prev&4 or v&14)
                if cost<=budget:best[key]=min(cost,best.get(key,cost))
        return tuple(sorted((*k,v) for k,v in best.items()))
    states=[start];ids={start:0};rows=[];ends=[]
    for s in states:
        ends.append(tuple(b for b in (0,1) if any(e+p<=budget for _,_,p,e in bit(s,b))))
        row=[]
        for word in product((0,1),repeat=3):
            t=s
            for b in word:t=bit(t,b)
            j=ids.setdefault(t,len(ids))
            if j==len(states):states.append(t)
            row.append(j)
        rows.append(row)
    # Moore refinement, with the two possible last bits as output.
    labels=[0]*len(states)
    while True:
        sig={};new=[sig.setdefault((e,tuple(labels[j] for j in r)),len(sig))
                    for e,r in zip(ends,rows)]
        if labels==new:break
        labels=new
    reps=[labels.index(i) for i in range(len(sig))]
    return [tuple(labels[j] for j in rows[i]) for i in reps],[ends[i] for i in reps]

def audit(budget):
    rows,end=language(budget)
    dead=next(i for i,r in enumerate(rows) if not end[i] and set(r)=={i})
    @lru_cache(None)
    def bounds(i):
        loops=[a for a,j in enumerate(rows[i]) if i==j]
        assert len(loops)<=1 and all(a in (0,1,2,4,7) for a in loops)
        below=[bounds(j) for j in set(rows[i])-{i,dead}]
        return (int(bool(loops))+max((x for x,y in below),default=0),
                max((y+1 for x,y in below),default=0))
    print('bill',budget,'minimal states',len(rows),'max long pieces / exceptional triples',bounds(0))
    if budget==1:
        for i,r in enumerate(rows):
            if i!=dead:print(i,','.join(f'{a:03b}:{j}' for a,j in enumerate(r) if j!=dead),'end',end[i])
if __name__=='__main__':
    for e in range(3):audit(e)
