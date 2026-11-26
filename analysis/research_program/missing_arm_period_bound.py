"""Period-independent deficit obstruction for a glued pair of identical cuts."""
from collections import defaultdict
from .western_cut_transfer import north_star_union

def recurrent(words,F,reverse):
    # Vertices are two successive longitudinal masks in one column.
    # A transverse period, of *any* length, walks inside a single SCC.
    adj=defaultdict(set)
    for a,b,c,d in words:
        if reverse:a,b,c,d=b,a,d,c
        if a in F and c in F:adj[a,b].add((c,d))
    def reach(x):
        out=set();q=[x]
        for v in q:
            for w in adj.get(v,()):
                if w not in out:q.append(w);out.add(w)
        return out
    R={x:reach(x) for x in set(adj)|set().union(*adj.values())}
    return {frozenset(y for y in R[x] if x in R[y]) for x in R if x in R[x]}

def check():
    BT=north_star_union()
    transverse={73,146,292}
    for v in range(13):
        ws=BT[6,v]
        for a,b,c,d in ws:
            for x,y in ((a,c),(b,d)):
                if x.bit_count()==y.bit_count()==3:
                    assert x==y and x in transverse|{7,56,448}
    for l,m,r in ((6,7,3),(48,56,24),(384,448,192)):
        F={l,m,r}
        for v in range(13):
            for rev in (False,True):
                for g in recurrent(BT[6,v],F,rev):
                    outs={b for a,b in g}
                    assert outs<=F or len(outs)==1 and outs<=transverse
            # Inside F, distinguish the clipped north/south endpoints and
            # disallow a clipped tile reappearing in the interior.
            for a,b,c,d in BT[6,v]:
                if {a,b,c,d}<=F:
                    assert a!=r and b!=l
                    if v==0:assert a==l
                    if v==12:assert b==r
        print('from full mask',m,'all rooted continuations stay in',sorted(F),
              'forcing a marked north-to-south path')
    print('any transverse period: every longitudinal slice loses at least one mark')
if __name__=='__main__':check()
