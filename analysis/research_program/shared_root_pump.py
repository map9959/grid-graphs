"""For each COMMON mark word retain its complete single-orientation relation.

Four choices from one record give four orientations of that same word.
Taking the fourth Cartesian power after union over words would be unsound.
"""
from .joint_rim_pump import kernel
from functools import lru_cache
from collections import defaultdict

def check(H,period=42,interior=False,row0=0,trimpath=False):
    assert period%3==0
    cols,arcs,extend=kernel(H,interior,row0);initial=tuple(range(H))*2
    if trimpath:initial=(initial,initial)
    @lru_cache(maxsize=60000)
    def choices(j,a,b,R):
        by=defaultdict(set)
        for entry,west,used in R:
            for c,nw,pay in arcs(j,a,b,west):
                if not (used and pay):by[c].add((entry,nw,used or pay))
        return [(c,frozenset(s)) for c,s in by.items()]
    pairs=peak=L=0
    for a0 in cols:
        for b0 in cols:
            if a0&((b0<<1)|(b0>>1)):continue
            R=frozenset((w,w,0) for w in range(1<<H) if not w&~(a0|b0) and arcs(12,a0,b0,w))
            if not R:continue
            pairs+=1;dp={(a0,b0,initial,R)};early={}
            for t in range(94):
                peak=max(peak,len(dp))
                if t>=9 and t%3==0:
                    if early.pop(t-period,None)==dp:L=max(L,t-period);break
                    early[t]=dp
                nd=defaultdict(set)
                for a,b,p,R in dp:
                    for c,T in choices(12+t%3,a,b,R):
                        if trimpath:
                            u=extend(b,c,p[0])
                            if u is not None:u=(u,extend(b,c,p[1],trimpath))
                        else:u=extend(b,c,p)
                        if u is not None:nd[b,c,u].add(T)
                dp=set()
                for key,rs in nd.items():
                    # For the same end marks and port partition a single
                    # superset word realizes every quadruple of the subset.
                    kept=[]
                    for T in sorted(rs,key=len,reverse=True):
                        if not any(T<=V for V in kept):kept.append(T);dp.add((*key,T))
            else:raise AssertionError(('no 42 repeat',a0,b0,len(dp)))
    kind='core' if interior else 'side'
    print(f'H={H} {kind}: shared-word relation {L} = {L+period}; {pairs} entry mark pairs; peak {peak} undominated records per pair',flush=True)
    return L
if __name__=='__main__':
    import sys
    check(int(sys.argv[1]))
