"""Necessary adjacent patch-marginal identities for a joint thirteen-row flow."""
from .seven_threshold import Counter,defaultdict,MASKS,fine_axis

def overlaps(l,height=13):
    # Exact marginal identities implied by summing the strip flow. The
    # boundary between phases must be handled separately where a phase
    # has more than one successor. Aggregate over each common edge type
    # only where both endpoint phase sums cover the same columns.
    eq=set()
    def compare(la,lb,proj0,proj1):
        v=defaultdict(Counter)
        for m in MASKS:
            v[proj0(m)][la(m)]+=1;v[proj1(m)][lb(m)]-=1
        for t in v.values():
            terms=tuple(sorted((x,w) for x,w in t.items() if w))
            if terms:eq.add(terms)
    hs={fine_axis(j,height) for j in range(107)}
    for r in range(height-3):
        for h in hs:
            compare(lambda m:l[h,r,m],lambda m:l[h,r+1,m],lambda m:m>>3,lambda m:m&63)
    # Bipartite phase-incidence components include the two ends of the
    # periodic middle. Each physical adjacent pair occurs once on both sides.
    groups=[]
    for j in range(106):
        g={(0,fine_axis(j,height)),(1,fine_axis(j+1,height))}
        for c in groups.copy():
            if c&g:g.update(c);groups.remove(c)
        groups.append(g)
    for g in groups:
        for r in range(height-2):
            v=defaultdict(Counter)
            for side,h in g:
                for m in MASKS:
                    v[(m if side else m>>1)&219][l[h,r,m]]+=-1 if side else 1
            for cs in v.values():
                t=tuple(sorted((x,w) for x,w in cs.items() if w))
                if t:eq.add(t)
    return sorted(eq)
