"""Construct a shared, one-pass transfer certificate on cramped rectangles.

Only retain transitions used by successful cases. The Lean verifier checks
each transition against the full bank and separately traces the rectangles.
"""
from functools import lru_cache
from pathlib import Path
from .root_cover_wave import edges


def cramped(u):
    k = 11 + 14*u
    return [q for q in range(1, min(55,k-2)+1,2) if 4*(max(3,q+1)+12)>k+3]


@lru_cache(None)
def move(s,e,top,north,west):
    output=[(b,r) for n,w,b,r in edges(s,e,top)
            if (north is None or n in north) and (west is None or w in west)
            and (e or all(x & 5 != 5 for x in divmod(r,1024)))]
    return frozenset(b for b,_ in output),frozenset(r for _,r in output)


def trial(h,w):
    trace=set()
    ns=[None]*(w-1)
    for r in range(h-1):
        west=None
        for c in range(w-1):
            args=(min(6,h-2-r),min(6,w-2-c),r==0,ns[c],west)
            ns[c],west=move(*args)
            trace.add(args)
    return trace if not west else None


def run():
    sets={None:0}  # no neighbor; id 1 is the empty set
    def idx(s):return sets.setdefault(s,len(sets))
    idx(frozenset())
    transitions=set()
    total=0
    for u in range(3,19):
        k=11+14*u
        qs=cramped(u)
        passed=[]
        for q in qs:
            trace=trial(k-4,k-max(3,q+1)-12)
            if not trace:break
            passed.append(q)
            for s,e,top,n,w in sorted(trace,
                    key=lambda z:(z[:3],*(tuple(sorted(x)) if x is not None else (-1,) for x in z[3:]))):
                below,right=move(s,e,top,n,w)
                transitions.add((s,e,int(top),idx(n),idx(w),idx(below),idx(right)))
            total+=1
        print(u,passed,flush=True)
    p=Path('lean/GridGraphs/ResidueTwoUpper/OneGap/CrampedTransfer.txt')
    p.write_text('\n'.join([' '.join(map(str,sorted(s or []))) for s in sets])
                 +'\n#\n'+'\n'.join(' '.join(map(str,z)) for z in sorted(transitions))+'\n')
    print(total,'excluded;',len(sets),'sets',len(transitions),'transitions',p.stat().st_size,'bytes')


if __name__=='__main__':run()
