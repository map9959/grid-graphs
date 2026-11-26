"""Abstract one-pass labelled support by signed distance to a diagonal.
Tests least closure, not coinductive self-support. This is a diagnostic:
soundness for physical boards needs a checked closed table."""
from .east_rail_fold import catalogue
from functools import lru_cache

@lru_cache(None)
def edges(s,e,top,mixed_rim=False):
    vs=catalogue()[1 if s==6 else 38-s,0 if e==6 else 31-e]
    out=[]
    for a,b,c,d in vs:
        if top and (b!=73 or (a!=73 and not (mixed_rim and a==9))):continue
        for x in ((1,) if top else (0,1)):
            for y in ((1,) if top else (0,1)):
                z=int(bool(x and a&8 and (a&64 or c&1)))
                t=int(bool(y and b&8 and (b&64 or d&1)))
                if (x and y and a&2 and b&1 or z and t and c&2 and d&1
                    or not s and (z and c&8 or t and d&8)
                    or mixed_rim and not e and (y and b&2 or t and d&2)):continue
                A,B,C,D=2*a+x,2*b+y,2*c+z,2*d+t
                out.append((1024*A+B,1024*A+C,1024*C+D,1024*B+D))
    return tuple(out)

def close(lo=-6,hi=9,slack=None,mixed_rim=False):
    ts=range(lo,hi+1)
    clamp=lambda t:max(lo,min(hi,t))
    # Actual s,e may exceed the displayed values when at 6.
    def realizable(s,e,t):
        if slack is None:return True
        if s==e==6:return True
        if s==6:return t>=clamp(slack+3*s-4*e)
        if e==6:return t<=clamp(slack+3*s-4*e)
        return t==clamp(slack+3*s-4*e)
    ids=[(s,e,t) for s in reversed(range(7)) for e in reversed(range(7)) for t in ts if realizable(s,e,t)]
    g={p:(set(),set()) for p in ids}
    for it in range(150):
        ch=0
        for s,e,t in ids:
            z,r=g[s,e,t]
            tops=[clamp(t+3)] if t!=lo else list(range(lo,lo+4))
            lefts=[clamp(t-4)] if t!=hi else list(range(hi-4,hi+1))
            N=set().union(*(g.get((min(6,s+1),e,i),(set(),set()))[0] for i in tops))
            W=set().union(*(g.get((s,min(6,e+1),i),(set(),set()))[1] for i in lefts))
            west=e==6 and t<=0
            for top in (0,1) if s==6 and t>=0 else (0,):
                for n,w,b,k in edges(s,e,top,mixed_rim):
                    if (top or n in N) and (west or w in W):
                        if b not in z:z.add(b);ch+=1
                        if k not in r:r.add(k);ch+=1
        if not ch:break
    print(lo,hi,slack,'iterations',it,'terminal pairs',
          [len(g[0,0,clamp(i)][0]) for i in (7,9)],flush=True)
    return g

if __name__=='__main__':
    import sys
    from pathlib import Path
    mixed=sys.argv[1:]==['--export-mixed']
    lo,hi=(-4,3) if mixed else (-1,6)
    g=close(lo,hi,mixed_rim=mixed)
    if mixed or sys.argv[1:]==['--export']:
        # Printable certificate. The Lean verifier checks inductiveness
        # and terminal emptiness directly, not the search for these sets.
        pool={}
        ids=[]
        for s in range(7):
            for e in range(7):
                for t in range(lo,hi+1):
                    for xs in g[s,e,t]:
                        key=tuple(sorted(xs))
                        ids.append(pool.setdefault(key,len(pool)))
        path=Path('lean/GridGraphs/ResidueTwoUpper/OneGap')/('MixedRimWave.txt' if mixed else 'RootCoverWave.txt')
        lines=[' '.join(map(str,ids))]+[' '.join(map(str,x)) for x in pool]
        path.write_text('\n'.join(lines)+'\n')
        print('certificate',len(pool),'sets,',path.stat().st_size,'bytes')
