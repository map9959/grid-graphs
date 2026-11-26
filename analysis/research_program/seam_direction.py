"""Arbitrary-length support relaxation of the cross tariff near the isolate."""
from .cross_seam_bound import ht,horizontal,rowchart,BASE,push,sym
from collections import defaultdict

K=39
Q=19
LOOPS=(8,28)

def cone(axis,j,q=Q):
    """All horizontal extensions west and east of the observed star halo."""
    loops=tuple(x for x in LOOPS if (x!=8 or q>=Q) and (x!=28 or q<=Q))
    ts=[ht(axis,rowchart(x,K),j,max(-4,min(5,q-x))) for x in range(K-1)]
    st={(w,z) for w in ts[0] if (z:=horizontal(BASE,w,True,j)) is not None}
    def edges(p,x):
        w,z=p;end=x==K-2
        for y in ts[x].get(w,()):
            h=horizontal(z,y,end,j)
            if h is not None and (not end or 2 not in h[2]):yield y,h
    history=[];rev={}
    for x in range(K-1):
        if x in loops:
            rev[x]=defaultdict(list);todo=list(st)
            for p in todo:
                for n in edges(p,x):
                    rev[x][n].append(p)
                    if n not in st:st.add(n);todo.append(n)
        history.append(st);st={v for p in st for v in edges(p,x)}
    out={}
    for x in reversed(range(K-1)):
        prev=set();allowed=defaultdict(set)
        for p in history[x]:
            for n in edges(p,x):
                if n not in st:continue
                prev.add(p)
                a,b=p[0];c,d=n[0];allowed[a,c].add((b,d))
        if x in loops:
            todo=list(prev)
            for p in todo:
                for n in rev[x][p]:
                    if n not in prev:prev.add(n);todo.append(n)
        out[x]=allowed;st=prev
    return out

def vertical(tabs,r,kinds):
    # Record which types actually occur, allowing arbitrarily many of each.
    allow={0}|{v<<(2*b) for v in kinds for b in range(3)}
    def flag(w):
        x=sym(w)
        return 0 if not x else 1<<(((x|x>>2|x>>4)&3)-1)
    st={(w,z,flag(w)) for w in tabs[0] if sym(w) in allow and (z:=push(BASE,w,True,r)) is not None}
    def nxt(p,j):
        w,z,used=p;end=j==K-2
        for y in tabs[rowchart(j,K)].get(w,()):
            if sym(y) not in allow:continue
            h=push(z,y,end,r)
            if h is not None and (not end or 2 not in h[2]):yield y,h,used|flag(y)
    for j in range(K-1):
        if j==18:
            todo=list(st)
            for p in todo:
                for n in nxt(p,j):
                    if n not in st:st.add(n);todo.append(n)
        st={n for p in st for n in nxt(p,j)}
    return {p[2] for p in st}

def check(axis):
    exceptions=[];last=set();ends=set()
    for q in range(1,K-1):
        sets={j:cone(axis,j,q) for j in sorted({rowchart(y,K) for y in range(K-1)})}
        def status(i,kinds):
            return vertical({j:t[i] for j,t in sets.items()},rowchart(i,K),kinds)
        for i in range(max(0,q-5),q):
            if 4 in status(i,(3,)):exceptions.append((q,i))
        last.update(status(K-2,(1,2,3)))
        for i in range(K-6,K-1):ends.update(status(i,(1,3)))
        if q==Q:
            assert 4 in status(q-6,(3,)) and 4 in status(q,(3,))
    print('axis',axis,'surviving (base q,cut) exceptions to no pure-east word in halo',exceptions,flush=True)
    print('last cut type masks',sorted(last),'last five cut masks without west skip',sorted(ends))
    assert exceptions==[(3,0),(5,0),(5,1),(7,2)] and last=={2,3,6,7}
if __name__=='__main__':
    import sys
    for a in map(int,sys.argv[1:] or (1,2)):check(a)
