"""Complete an incomplete aligned frame, removing one unprotected owner per cycle."""
from .comb_cap_transfer import construct
from .extend_forest_28 import verify

def repair(rows,a,b):
    n=len(rows);L=3;R=n-4
    marks={(y,x) for y,row in enumerate(rows) for x,c in enumerate(row) if c=='#'}
    D=({(y,x) for y in (a,b) for x in range(L,R+1,3)}|
       {(y,x) for y in range(a,b+1) for x in (L,R)})
    missing=D-marks
    guard={(y,x) for y in (a,b) for x in range(L,R+1) if (x-L)%3}
    for y,x in missing:
        guard.update((y+dy,x+dx) for dy,dx in ((0,-1),(0,1),(0,-2),(0,2),
                                                 (-1,-1),(-1,1),(1,-1),(1,1)))
    assert not guard&D
    removed=marks&guard;marks=(marks-removed)|missing
    def cycle():
        parent={};done=set()
        for root in marks:
            if root in parent:continue
            parent[root]=None;todo=[(root,0)]
            while todo:
                u,k=todo.pop()
                if k==4:done.add(u);continue
                todo.append((u,k+1));dy,dx=((-1,0),(0,1),(1,0),(0,-1))[k]
                v=u[0]+dy,u[1]+dx
                if not(0<=v[0]<n and 0<=v[1]<n) or not({u,v}&marks):continue
                if v==parent[u] or v in done:continue
                if v not in parent:parent[v]=u;todo.append((v,0));continue
                path=[u]
                while path[-1]!=v:path.append(parent[path[-1]])
                return path
    paid=0
    while (c:=cycle()):
        for i,u in enumerate(c):
            owners={u,c[i-1]}&marks
            if len(owners)==1 and not owners&D:
                marks-=owners;paid+=1;break
        else:raise AssertionError('cycle has no deletable owner')
    assert paid<=len(missing)
    out=[''.join('#' if (y,x) in marks else '.' for x in range(n)) for y in range(n)]
    return len(removed),len(missing),paid,verify(out)

if __name__=='__main__':
    n=103;a=3;b=93;r=construct(n,4)
    # Transposition gives a physical forest with many incomplete vertical
    # runs at the specified x's. No assumption on the number of holes.
    for rows in (r,[''.join(x) for x in zip(*r)]):
        print('off-profile deletions, insertions, cycle repairs, tree:',repair(rows,a,b))
