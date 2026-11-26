"""A local rooted block loses at most three columns per four rows."""
from .synchronous_front import cell,Pool,prune,rowchart
from .odd_fan_bulk import STRAIGHT

def window(W,H,south):
    P=Pool();g=[]
    for j in range(H-1):
        v=rowchart(j+14,H+14) if south else 7
        d=cell(1,7,v,-4)&cell(2,7,v,-4)
        g.extend([P.intern(frozenset(t for t in d if j or t[0]==t[2]==7))]*(W-1))
    ok=prune(g,P,W,H,(),0,south,sides=0)
    if south:return not ok
    assert ok
    for j in range(4):
        for x in range(3,W):
            i=min(x,W-2);off=2*(x-i)
            assert all(p[off]==p[off+1]==7 for p in P.items[g[j*(W-1)+i]])
    return True

def audit():
    assert window(10,10,False)
    for h in range(20,24):
        assert window(26,h,True)
    print('open-sided 10-column window: retreat <=3/4; 26 rooted columns reject all four south ends')
    W=18;H=24;P=Pool();d=frozenset(t for t in cell(1,7,7,-4) if set(t)<=STRAIGHT)
    g=[P.intern(d if j else frozenset(p for p in d if p[0]==p[2]==7)) for j in range(H-1) for _ in range(W-1)]
    assert prune(g,P,W,H,(),W,sealed=range(W),sides=0)
    for j in range(13):
        assert all(t[0]==t[1]==7 for t in P.items[g[j*(W-1)+6]])
    for r in range(7,38):
        assert all(t[2]==7 for t in cell(1,r,7,-4) if t[0]==7)
    print('dangling window: column 6 survives 13 rows; its eastern neighbors follow')
    W=64
    for H in range(31,44):
        P=Pool();g=[]
        for j in range(H-1):
            for i in range(W-1):
                r,v=rowchart(i+14,W+14),rowchart(j+14,H+14)
                d=cell(1,r,v,-4)&cell(2,r,v,-4)
                g.append(P.intern(d if j else frozenset(t for t in d if t[0]==t[2]==7)))
        assert not prune(g,P,W,H,(),W-1,True,sides=2)
    print('64-column east cap: one rooted line suffices at heights 31..43')
if __name__=='__main__':audit()
