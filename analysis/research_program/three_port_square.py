"""Exact deficit spectra of the ordered three- and four-hop relaxations."""
from collections import defaultdict
from functools import lru_cache
from .ordered_ports import relation

EMPTY=(),(),()

@lru_cache(None)
def edges(axis,r,d,cap=3):
    phase=4 if d==5 else -4 if d==-4 else None
    rel=relation(axis,r,cap=cap,phase=phase,offset=d,ends=True,exact=True)
    out=defaultdict(list);canonical={}
    for p,q,c in rel:
        assert c>=0
        out[p].append((canonical.setdefault(q,q),c))
    return out

def move(st,axis,r,cap=3):
    out={}
    for (p,d),bits in st.items():
        if r>=32 and d>37-r:continue
        for q,c in edges(axis,r,d,cap).get(p,()):
            for e in ((4,5) if d==5 else (max(-4,d-1),)):
                key=q,e
                out[key]=out.get(key,0)|(bits<<c)
    return out

def run(axis,cap=3):
    assert axis in (1,2) and cap in (3,4)
    def step(st,r):return move(st,axis,r,cap)
    st={(EMPTY,d):1 for d in range(1,6)}
    for r in range(7):st=step(st,r)
    # Structural backward trim, independent of deficit and length.
    reach=set(st);todo=list(reach);pred=defaultdict(set)
    for p in todo:
        for q in step({p:1},7):
            pred[q].add(p)
            if q not in reach:todo.append(q);reach.add(q)
    layers=[reach]
    for r in range(32,39):layers.append(set(step(dict.fromkeys(layers[-1],1),r)))
    good=layers[-1]
    assert all(p==EMPTY for p,d in good)
    for r in reversed(range(32,39)):
        good={p for p in layers[r-32] if good.intersection(step({p:1},r))}
    todo=list(good)
    for q in todo:
        for p in pred[q]:
            if p not in good:good.add(p);todo.append(p)
    # Retain exact costs of each useful edge and every accepting suffix,
    # so the certificate does not rebuild the fringe at every induction.
    graph={s:{q:v for q,v in step({s:1},7).items() if q in good} for s in good}
    def costs(bits):
        while bits:
            b=bits&-bits;yield b.bit_length()-1;bits-=b
    graph={s:[(q,c) for q,v in es.items() for c in costs(v)] for s,es in graph.items()}
    def bulk(st):
        out={}
        for p,b in st.items():
            for q,c in graph.get(p,()):out[q]=out.get(q,0)|(b<<c)
        return out
    suffix=dict.fromkeys(layers[-1],1)
    for r in reversed(range(32,39)):
        nxt={}
        for p in layers[r-32]:
            bits=0
            for q,v in step({p:1},r).items():
                if q in suffix:
                    for c in costs(v):bits|=suffix[q]<<c
            if bits:nxt[p]=bits
        suffix=nxt
    def finish(st):
        b=0
        for p,mask in st.items():
            for c in costs(suffix.get(p,0)):b|=mask<<c
        return b
    print('reachable/coreachable',len(reach),len(good),flush=True)
    for d in range(1,6):
        west={(EMPTY,d):1}
        for r in range(7):west=step(west,r)
        print('initial isolate offset',d,'viable bulk entry profiles',len(west.keys() & good))
    west=st
    for _ in range(25):st=bulk(st)
    saved=st
    for t in range(3 if cap==3 else 13):
        bits=finish(st)
        D=198+72*t
        print(axis,t,'min/count/max',(bits&-bits).bit_length()-1,bits.bit_count(),bits.bit_length()-1,
              'budget',D,'present',bool(bits>>D&1),flush=True)
        if cap==3:assert bits==(1<<234,1<<324,0)[t]
        else:assert bits>>D&1
        for _ in range(14):st=bulk(st)
    if cap==4:
        from .four_port_pump import certificate
        assert certificate(graph,west,suffix,axis),'no verified induction'
        return
    assert st=={s:b<<252 for s,b in saved.items()}
    print('42-column translation: all live spectra shift by exactly 252')
if __name__=='__main__':
    import sys
    run(*map(int,sys.argv[1:]))
