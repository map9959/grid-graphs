"""Unrestricted residue-one cuts priced by run starts and true isolates.

Column masks (bits 0..3) are the row just above a three-row block, then
its three rows A,B,C. The output word is B. Retain a single physical
forest on all four rows. Bounds are on the *number* of intervals, not
their lengths or the number of distinct masks.
"""
from collections import deque
from functools import lru_cache

@lru_cache(None)
def edge(old,part,v):
    if old>=0 and v&(old<<1|old>>1):return
    p=[*part,*range(4,8)]
    def rt(x):
        while p[x]!=x:x=p[x]
        return x
    def join(a,b):
        a,b=rt(a),rt(b);p[a]=b;return a!=b
    for i in range(4):
        if old>=0 and (old|v)>>i&1 and not join(i,i+4):return
        if i and v>>(i-1)&3 and not join(i+3,i+4):return
    z=[rt(i) for i in range(4,8)]
    return tuple(z.index(i) for i in z)

def check(budget,clip=16):
    # Greedy parsing into substrings of 000.., 111.., and all cyclic
    # shifts of 100100... . Longest possible first piece is optimal:
    # replacing a shorter first piece only removes/trims later pieces.
    init=(-1,tuple(range(4)),False,0,0,31,0,0)
    seen={init};q=deque([init]);maxpieces=0;badpure=False
    while q:
        old,part,pending,paid,x,possible,pieces,length=q.popleft()
        for v in range(16):
            z=edge(old,part,v)
            if z is None:continue
            prev=max(0,old)
            bill=paid+(v&14&~(v<<1)&~prev).bit_count()+int(pending and not(v&4))
            if bill>budget:continue
            pend=not ((prev&4) or (v&14))
            yes=(1<<x)|8
            opt=yes if v&4 else 31^yes
            live=possible&opt
            num=1 if old<0 else min(clip,pieces+int(not live))
            live=live or opt
            xx=(x+1)%3
            if length>=3 and xx==1 and bill+int(pend)<=budget:
                maxpieces=max(maxpieces,num)
                if not budget and (num!=1 or not live&1):badpure=True
            st=(v,z,pend,bill,xx,live,num,min(3,length+1))
            if st not in seen:seen.add(st);q.append(st)
    print('bill',budget,'reachable',len(seen),'maximum pieces',maxpieces,flush=True)
    assert maxpieces<clip
    if not budget:assert not badpure
    return maxpieces
def uniform():
    """Longest path with integer weight (additional pieces - twice the bill)."""
    init=(-1,tuple(range(4)),False,0,31,0)
    ids={init:0};states=[init];edges=[];accept=[]
    for u,(old,part,pending,x,possible,length) in enumerate(states):
        if x==1 and length==3:accept.append((u,2*int(pending)))
        for v in range(16):
            z=edge(old,part,v)
            if z is None:continue
            prev=max(0,old)
            bill=(v&14&~(v<<1)&~prev).bit_count()+int(pending and not(v&4))
            yes=(1<<x)|8;opt=yes if v&4 else 31^yes;live=possible&opt
            st=(v,z,not (prev&4 or v&14),(x+1)%3,live or opt,min(3,length+1))
            gain=int(old>=0 and not live)-2*bill
            j=ids.setdefault(st,len(ids))
            if j==len(states):states.append(st)
            edges.append((u,j,gain))
    val=[None]*len(states);val[0]=0
    for _ in states:
        changed=False
        for u,j,g in edges:
            if val[u] is not None and (val[j] is None or val[j]<val[u]+g):
                val[j]=val[u]+g;changed=True
        if not changed:break
    assert not changed,'positive-weight circuit'
    worst=max(val[u]-debit for u,debit in accept)
    assert worst==0
    print(len(states),'states',len(edges),'inequalities: pieces <= 1+2*bill at all widths 3k+1')
if __name__=='__main__':
    uniform()
    for b in range(5):check(b)
