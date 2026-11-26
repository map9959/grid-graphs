"""Necessary local clauses for a maximum forest, by a two-for-one tooth exchange."""
from .cross_rail_slab import repair
from .extend_forest_28 import verify


def clauses(n,i,j,vertical=True):
    """Yields (negative sites, positive sites) with pairs anchored at their start."""
    def pt(u,v):
        return (i+u,j+v) if vertical else (i+v,j+u)
    def inside(p):return all(0<=v<n for v in p)
    def block(u):
        return {pt(a,b) for b in (-1,1) if inside(pt(u,b)) for a,b in
                ((u,b),(u,2*b),(u-1,b),(u+1,b)) if inside(pt(a,b))}
    s=pt(0,0);t=pt(1,0);above=pt(-1,0)
    yield ({above,t} if inside(above) and inside(t) else set()),({s}|block(0))
    if inside(t):yield set(),({s,t}|block(0)|block(1))


def forbid(f,X,n,domain=None):
    for i,j in (domain if domain is not None else ((i,j) for i in range(n) for j in range(n))):
        for v in (True,False):
            for neg,pos in clauses(n,i,j,v):
                if domain is None or (neg|pos)<=domain:
                    f.append([-X[a*n+b] for a,b in sorted(neg)]+[X[a*n+b] for a,b in sorted(pos)])


def pack(rows):
    """One pitch phase: maximum interval packing in each rail, all six choices."""
    n=len(rows);best=[]
    for vertical in (True,False):
        banks=[[] for _ in range(3)]
        for rail in range(n):
            offers=[]
            for t in range(n):
                i,j=(t,rail) if vertical else (rail,t)
                for z,(neg,pos) in enumerate(clauses(n,i,j,vertical)):
                    if all(rows[u][v]=='#' for u,v in neg) and all(rows[u][v]=='.' for u,v in pos):
                        offers.append((t+z,t))
            last=-1
            for end,t in sorted(offers):
                if t>last:
                    banks[rail%3].append([(u,rail) if vertical else (rail,u) for u in range(t,end+1)])
                    last=end
        best=max([best,*banks],key=len)
    return best


def packed_replay(rows):
    bank=pack(rows)
    rr=[list(s) for s in rows]
    for move in bank:
        for y,x in move:rr[y][x]='#'
    rr,dropped=repair(rr)
    tree=verify(rr)
    assert dropped<=sum(len(m)-1 for m in bank)
    assert tree[0]>=sum(s.count('#') for s in rows)+len(bank)
    return len(bank),dropped,tree


def replay():
    n=10
    holes={(0,1),(1,9),(9,8),(8,0),(4,9),(5,9)}
    board=[''.join('#' if min(i,j,9-i,9-j)==0 and (i,j) not in holes else '.'
                   for j in range(n)) for i in range(n)]
    start=verify(board)
    neg,pos=list(clauses(n,4,9))[1]
    assert not neg and not any(board[i][j]=='#' for i,j in pos)
    from .reflected_pitch_rank import ledger
    for added in [(4,),(5,),(4,5)]:
        out=board[:]
        for i in added:out[i]=out[i][:9]+'#'
        assert ledger(out)[0]==1
    end,dropped=repair(out);tree=verify(end)
    assert dropped==1 and tree[0]==start[0]+1
    print('both single insertions cyclic; joint cycle rank 1; repaired trees',start,tree)


if __name__=='__main__':
    replay()
    from .cross_minor_refill import shell_control
    from .cross_minor_price import repair as compress,construct,scattered
    for rows,y,x in [(scattered(construct(103,4)),2,17),(shell_control(103),37,49)]:
        rr,q,p=compress(rows,y,x)
        moves,dropped,tree=packed_replay(rr)
        print('side 103 cut',(y,x),'input packing',len(pack(rows)),'cut packing',moves,
              'cycle repairs',dropped,'net loss',sum(r.count('#') for r in rows)-tree[0],'tree',tree)
