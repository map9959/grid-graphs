"""Compose ordered cut states with one shared isolate; no position resampling of rim masks."""
from functools import lru_cache
from collections import defaultdict
from .ordered_ports import relation

@lru_cache(None)
def adj(axis,r,d,upper):
    phase=4 if d==5 else -4 if d==-4 else None
    tab=relation(axis,r,phase=phase,offset=d,ends=True,upper=upper)
    out=defaultdict(list)
    for (p,q),v in tab.items():out[p].append((q,v))
    return out

def move(st,axis,r,upper=True):
    nd={}
    for (p,d),v in st.items():
        if r>=32 and d>37-r:continue
        for q,x in adj(axis,r,d,upper)[p]:
            for e in ((4,5) if d==5 else (max(-4,d-1),)):
                key=q,e
                if key not in nd or (v+x>nd[key] if upper else v+x<nd[key]):nd[key]=v+x
    return nd

def run(axis,upper=True):
    empty=(),(),()
    st={(empty,d):0 for d in (1,2,3,4,5)}
    for r in range(7):st=move(st,axis,r,upper)
    # Retain only bulk states which can reach the actual east boundary
    # after some number of steps. Compute reachability without costs.
    reach=set(st);todo=list(st);pred=defaultdict(set)
    for p in todo:
        for q in move({p:0},axis,7,upper):
            pred[q].add(p)
            if q not in reach:reach.add(q);todo.append(q)
    layers=[reach]
    for r in range(32,39):layers.append(set(move(dict.fromkeys(layers[-1],0),axis,r,upper)))
    good=layers[-1]
    assert all(p==empty for p,d in good)
    for r in reversed(range(32,39)):
        good={p for p in layers[r-32] if good.intersection(move({p:0},axis,r,upper))}
    todo=list(good)
    for q in todo:
        for p in pred[q]:
            if p not in good:good.add(p);todo.append(p)
    def bulk(st):
        return {s:v for s,v in move(st,axis,7,upper).items() if s in good}
    print('axis',axis,'reachable/coaccessible',len(reach),len(good),flush=True)
    cycle=[((sig,(1,0),(6,6,192,192)),-4) for sig in ((7,2),(1,5),(4,8))]
    assert set(cycle)==good
    for p in sorted(good):
        assert bulk({p:0})=={cycle[(cycle.index(p)+1)%3]:6}
    # Check the actual starting isolate as well as its clipped offset.
    for d in range(1,6):
        start={(empty,d):0}
        for r in range(7):start=move(start,axis,r,upper)
        assert bool(start.keys() & good)==(d==1)
    for j in range(25):st=bulk(st)
    saved=st
    for t in range(3):
        end=st
        for r in range(32,39):end=move(end,axis,r,upper)
        ans=(max if upper else min)(end.values(),default=None)
        print(axis,'upper' if upper else 'lower',t,'bulk end states',len(st),'closed bound',
              ans,'budget',198+72*t,flush=True)
        assert ans==(234 if t==0 else None)
        for j in range(14):st=bulk(st)
    assert st=={s:v+252 for s,v in saved.items()}
    print('42 further tile columns: identical support, +252 deficit; only isolate distance 5 can enter')
if __name__=='__main__':
    import sys
    run(int(sys.argv[1]),'--min' not in sys.argv)
