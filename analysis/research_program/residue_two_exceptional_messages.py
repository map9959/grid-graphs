"""Extract a short acyclic proof of the exceptional star/patch charge filter.

No optimizer. At the budget of 72/1008 every individual occurrence is
cheap. A message excludes a projected event on one end of an incidence.
Its positive rank exceeds a blocking message at the other end of every
cheap atom that could have produced it. Only messages reached while
explaining an excluded charge are exported.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path

from .square_dual_physical import DIR, MASKS, SYM, inspect, trans
from .square_current import states


def axis(s, d, i):
    if i < d:
        return i
    return 2*d + 3 + i - s if i >= s-d else d + (i-d)%3


def table(frame=False):
    family = inspect(20)
    atoms = []
    support = defaultdict(list)
    for patch in (False, True):
        s, depth = (21, 5) if patch else (23, 6)
        for i,j in product(range(s), repeat=2):
            if any(depth+3 <= v < s-depth for v in (i,j)):
                continue
            def loc(n,d,r,c):
                return axis(n,d,r)*16 + axis(n,d,c)
            positions = [trans(i,j,s,g) for g in range(8)]
            fine = [(axis(s,depth,r),axis(s,depth,c)) for r,c in positions]
            dirs = [d for d,(a,b) in enumerate(DIR) if 0<=i+a<s and 0<=j+b<s]
            events = MASKS if patch else states(dirs)
            for ev in events:
                if patch:
                    m = ev
                    images = SYM[m]
                else:
                    f,sig = ev
                    out = next((d for d in dirs if sig[d][2]==(1 if d<2 else -1)), -1)
                    nb = [sig[d][int(d<2)] if d in dirs else 9 for d in range(4)]
                    images = []
                    for g in range(8):
                        def turn(d):
                            return ((2-d if g&4 else d)+(g&3))%4
                        word=[9]*4
                        for d,v in enumerate(nb):
                            word[turn(d)]=v
                        images.append((f,tuple(word),turn(out) if out>=0 else -1))
                w=family['p' if patch else 's',min(zip(fine,images))]*1008
                assert w.denominator == 1
                if w>72:
                    continue
                if frame and (w not in (0,72) or (not patch and len(dirs)==2 and not f)):
                    continue
                incidences = []
                for a,b in product(range(3),repeat=2):
                    r,c=(i,j) if patch else (i-a,j-b)
                    if not (0<=r<21 and 0<=c<21):
                        continue
                    q=3*a+b
                    bits=[(m>>q)&1 if patch else f]
                    for d,(dr,dc) in enumerate(DIR):
                        if 0<=a+dr<3 and 0<=b+dc<3:
                            bits.append((m>>(q+3*dr+dc))&1 if patch else nb[d])
                    event=sum(bit<<l for l,bit in enumerate(bits))
                    key=(((loc(21,4,r,c)*256+loc(23,5,r+a,c+b))*9+q)*64+event)
                    incidences.append(key)
                    support[patch,key].append(len(atoms))
                if not frame:
                    good=w in (0,36,54,72)
                elif patch:
                    rr,cc=min(i,s-1-i),min(j,s-1-j)
                    good=w==0 or (rr>0 and cc>0)
                    if rr==cc==0:
                        def near(a,b):
                            return (m>>(3*(2-a if i else a)+(2-b if j else b)))&1
                        word=tuple(near(a,b) for a,b in ((0,1),(0,2),(1,0),(2,0)))
                        good=good and word in ((0,0,1,1),(0,1,1,1),(1,1,0,0),(1,1,0,1))
                else:
                    rr,cc=min(i,s-1-i),min(j,s-1-j)
                    d=min(rr,cc)
                    inward=out!=-1 and min(i+DIR[out][0],j+DIR[out][1],
                        s-1-i-DIR[out][0],s-1-j-DIR[out][1])==1
                    good=not (d==0 and max(rr,cc)>=3 and not f or d==1 and f)
                    if d==0:
                        good=good and ((w==72)==inward)
                    elif w:
                        good=good and d==2 and not f and 1 not in nb and out==-1
                atoms.append((patch,good,incidences))
    alive = set(range(len(atoms)))
    blocker = {}
    ranks = {}
    for r in range(1,10):
        labels={(p,k) for u in alive for p,_,events in [atoms[u]] for k in events}
        for u in sorted(alive):
            p,_,ev=atoms[u]
            opts=[(not p,k) for k in ev if (not p,k) not in labels]
            if opts:
                for fact in opts:
                    ranks.setdefault(fact,r)
                blocker[u]=opts
        alive.difference_update(blocker)
        if all(atoms[u][1] for u in alive):
            break
    else:
        raise AssertionError("inadequate propagation")
    used=set()
    @lru_cache(None)
    def complexity(fact):
        return 1+sum(min(complexity(b) for b in blocker[u] if ranks[b]<ranks[fact])
                     for u in support[fact])
    def explain(u,limit):
        opts=[b for b in blocker[u] if ranks[b]<limit]
        if any(b in used for b in opts):
            return
        b=min(opts,key=lambda a:(complexity(a),a))
        if b in used:
            return
        used.add(b)
        for other in support[b]:
            explain(other,ranks[b])
    for u,(_,good,_) in enumerate(atoms):
        if not good:
            explain(u,100)
    print('cheap types',len(atoms),'ranks',r,'messages',len(used))
    return sorted((2*k+int(p),ranks[p,k]) for p,k in used)


if __name__=='__main__':
    import sys
    frame='--frame' in sys.argv
    pairs=table(frame)
    dest=Path(__file__).resolve().parents[2]/'lean/GridGraphs/ResidueTwoUpper/Data'/(
        'frame.msg' if frame else 'exceptional.msg')
    dest.write_text(''.join(f'{k} {v}\n' for k,v in pairs))
