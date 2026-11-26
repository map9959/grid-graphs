"""Local certificates for the bounded arithmetic cover; no square-size DP."""
from .rooted_window_speed import window,cell,Pool,prune,rowchart,STRAIGHT

def audit():
    for s,d,w,H in ((6,4,5,13),(13,7,8,20),(20,10,11,27),(27,13,14,34)):
        P=Pool();D=frozenset(p for p in cell(1,7,7,-4) if set(p)<=STRAIGHT)
        g=[P.intern(D if j else frozenset(p for p in D if p[0]==p[2]==7))
           for j in range(H-1) for i in range(w-1)]
        assert prune(g,P,w,H,(),w,sealed=range(w),sides=0)
        for j in range(s):
            i=min(d-1,w-2);b=2*(d-1-i)
            assert all(p[b]==p[b+1]==7 for p in P.items[g[j*(w-1)+i]])
        print('dangling window',w,H,'retains column',d-1,'through row',s)
    assert window(10,10,False)
    for H in range(14,44):
        W=3*H//4+3;P=Pool();g=[]
        for j in range(H-1):
            for i in range(W-1):
                r,v=rowchart(i+14,W+14),rowchart(j+14,H+14)
                d=cell(1,r,v,-4)&cell(2,r,v,-4)
                g.append(P.intern(d if j else frozenset(t for t in d if t[0]==t[2]==7)))
        assert not prune(g,P,W,H,(),W-1,True,sides=2),H
    print('all 30 physical south caps empty')
if __name__=='__main__':audit()
