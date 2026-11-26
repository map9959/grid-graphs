"""Ledger-filtered one-to-two rail exchanges, keeping the two-gap boundary."""
from collections import Counter
from itertools import combinations
from .zipper_rails import build

DIR=((0,1),(1,0),(0,-1),(-1,0))
DIA=((-1,-1),(-1,1),(1,-1),(1,1))
def example(n):
    F=(n-5)//6; M=3*(F-(n-8-F)//7)
    x=(F+5,3*F+2);y=(n-6,M+2);z=(2,3)
    X={(i,j) for i,row in enumerate(build(n)) for j,b in enumerate(row) if b=='#'}
    def stats(X):
        left=set(X);rid={};runs=0
        while left:
            u=left.pop();q=[u];rid[u]=runs
            for i,j in q:
                for a,b in DIR:
                    v=i+a,j+b
                    if v in left:left.remove(v);rid[v]=runs;q.append(v)
            runs+=1
        p=list(range(runs));J=I=cycles=0
        def root(u):
            while p[u]!=u:p[u]=p[p[u]];u=p[u]
            return u
        for i in range(n):
            for j in range(n):
                if (i,j) in X:continue
                nb=[(i+a,j+b) for a,b in DIR if (i+a,j+b) in X]
                if not nb:I+=1
                if len(nb)==2:
                    a,b=map(lambda u:root(rid[u]),nb);J+=1
                    if a==b:cycles+=1
                    else:p[a]=b
                assert len(nb)<=2
        return len(X),runs,I,J,runs-J+cycles,cycles
    Y=(X-{x})|{y,z};a=stats(X);b=stats(Y);assert b[0]==a[0]+1 and b[1]==a[1]-2
    print('repeatable edit',n,'delete',x,'add',y,z,'(marks,runs,isolates,joins,components of joins,cycle rank)',a,'->',b)
def run(n):
    rows=build(n);X={(i,j) for i,row in enumerate(rows) for j,b in enumerate(row) if b=='#'}
    board={(i,j) for i in range(n) for j in range(n)}
    inside=lambda u:0<min(u) and max(u)<n-1
    def near(u,ds=DIR):return {(u[0]+a,u[1]+b) for a,b in ds}
    closed=lambda u:near(u)|{u}
    assert all(closed(u)&X for u in board)
    empty={u for u in board-X if inside(u)}
    valid={u for u in empty if not near(u,DIA)&X}
    d={u:len(near(u)&X) for u in valid}
    twos={u for u in valid if d[u]==2}
    assert len(twos)==1
    cnt=Counter();types=Counter()
    # A count-preserving relocation plus one new mark: three new marked
    # adjacencies NET are necessary since runs = marks - marked edges.
    for x in sorted(X):
        if not inside(x):continue
        dx=len(near(x)&X)
        if dx>=2:continue
        extra={u for u in near(x,DIA)&empty if near(u,DIA)&X=={x}}
        def deg(u):return (d[u] if u in valid else len(near(u)&X))-int(x in near(u))
        # Nonadjacent additions require a doubly supported site. Adjacent
        # additions can each have only one old end; then dx must be zero.
        pairs=set()
        V=valid|extra
        for y in twos|extra:
            if deg(y)==2:
                for z in V-{y}:pairs.add(tuple(sorted((y,z))))
        if dx==0:
            for y in V:
                for z in near(y)&V:pairs.add(tuple(sorted((y,z))))
        lost={u for u in closed(x)&board if closed(u)&X=={x}}
        for y,z in pairs:
            if z in near(y,DIA):continue
            if deg(y)+deg(z)+int(z in near(y))-dx!=3:continue
            cnt['score/run pass']+=1
            if lost-(closed(y)|closed(z)):continue
            cnt['no isolate']+=1
            # Check the contracted join graph, including parallel joins.
            Y=(X-{x})|{y,z};rid={};rr=0
            for u in Y:
                if u in rid:continue
                todo=[u];rid[u]=rr
                for v in todo:
                    for t in near(v)&Y:
                        if t not in rid:rid[t]=rr;todo.append(t)
                rr+=1
            assert rr==8*n//7-2
            p=list(range(rr));joins=cycles=0
            def root(i):
                while p[i]!=i:p[i]=p[p[i]];i=p[i]
                return i
            for u in board-Y:
                nbr=near(u)&Y;assert len(nbr) in (1,2)
                if len(nbr)==2:
                    a,b=(root(rid[v]) for v in nbr);joins+=1
                    if a==b:cycles+=1
                    else:p[a]=b
            cc=len({root(i) for i in range(rr)})
            assert joins==rr-1 and cc==cycles+1
            types[cc,cycles]+=1
            if cc==1:
                from .extend_forest_28 import verify
                witness=[''.join('#' if (i,j) in Y else '.' for j in range(n)) for i in range(n)]
                print('tree!',verify(witness),x,y,z);return
    print(n,'unique clean bridge',sorted(twos),'candidates',dict(cnt),'(components,cycle rank)',dict(types),flush=True)
if __name__=='__main__':
    import sys
    for n in map(int,sys.argv[1:]):example(n);run(n)
