"""Width-free two-row lookahead above each phase of the diagonal interface."""
from functools import lru_cache
from collections import defaultdict
import gzip,json
from pathlib import Path
from .interface_drift import full,K,S
from .tile_family_lp import typ

@lru_cache(None)
def column(z,m,rim,contact):
    old,pp=z;p=list(pp)+list(range(7,13))
    def rt(i):
        while p[i]!=i:i=p[i]
        return i
    def edge(i,j):
        a,b=rt(i),rt(j);p[a]=b;return a!=b
    for i in range(6):
        if old>=0 and (old|m)>>i&1 and not edge(i,7+i):return
        if i and m>>(i-1)&3 and not edge(6+i,7+i):return
        if rim and m>>i&1 and not edge(7+i,6):return
    if contact and not edge(12,6):return
    ids={};return m,tuple(ids.setdefault(rt(x),i) for i,x in enumerate((7,8,9,10,11,12,6)))

def check(axis):
    B={(u,v):ws for u,v,ws in json.loads(gzip.decompress(
        Path('target/tile_family_3_5_h6.json.gz').read_bytes()))}
    tabs=[]
    for j in range(K):
        by=defaultdict(set)
        for a,b,c,d in B[6,typ(j,K)]:
            if any(min(x,K-x)>=4 and m&16 and m&(40 if axis==1 else 130)
                   for x,m in ((j,a),(j+1,b),(j,c),(j+1,d))):continue
            by[c,d].add((a,b))
        tabs.append(by)
    P=[(16,16),(3,8,264),(33,32,384)]
    for h in range(3):
        old=full(P[h],S);want=full(P[(h+1)%3],S-(2 if h==0 else 1))
        cutoff=3*S+(2,4,3)[h]
        def step(z,w,j):
            for l in range(3):
                m=sum((v>>(3*a+l)&1)<<(3*t+a) for t,v in enumerate(w) for a in range(3))
                contact=3*j+l<cutoff and bool((old[j]>>l&1) or m&32)
                z=column(z,m,j in (0,K) and l==1,contact)
                if z is None:break
            return z
        def pairs(j):
            by=defaultdict(list);t=tabs[j]
            for c,d in t[old[j],old[j+1]]:
                for a,b in t[c,d]:by[a,c].append((b,d))
            return by
        def move(st,j):
            by=pairs(j);out=set()
            for w,z,diff in st:
                for y in by[w]:
                    s=step(z,y,j+1)
                    if s is not None:
                        mismatch,early,at=diff
                        out.add((y,s,(mismatch or y[1]!=want[j+1],
                                      early or (j+1<S and y[1]!=7),
                                      at or (j+1==S and y[1]==7))))
            return out
        st=set()
        for w in pairs(0):
            s=step((-1,tuple(range(7))),w,0)
            if s is not None:st.add((w,s,(w[1]!=want[0],w[1]!=6,False)))
        for j in range(K):
            st=move(st,j)
            if j in (8,23):
                # Kleene closure: any number of additional homogeneous
                # columns, independent on the two sides of the transition.
                extra=st.copy()
                while extra:
                    extra=move(extra,j)-st;st|=extra
        counts=(sum(not d[0] for w,z,d in st),sum(d[0] for w,z,d in st),
                sum(not d[1] and not d[2] for w,z,d in st),
                sum(not d[1] and d[2] for w,z,d in st))
        assert counts==(1,1,0,0)
        print(axis,P[h],'match / other / stationary / eastward terminal states',counts)

if __name__=='__main__':
    for a in (1,2):check(a)
