"""Exact period-(0,6) zigzag frontier: matching, score, and lifted primal connectivity."""
from collections import Counter,deque
from functools import lru_cache
from .period_nine import budgets
from .oblique_rails import arbitrary_arms

G=tuple(min(c,12-c) for c in range(12))
DIR=((1,0),(0,1),(0,-1))
@lru_cache(None)
def moves(occ):
    # Vertical always advances; horizontal advances on the descending side
    # of either arm of the staircase. At a turn this gives 1 or 3 choices.
    result=[]
    def add(c,taken,vertical):
        if c==12:
            result.append((taken,vertical));return
        if occ>>c&1:
            add(c+1,taken,vertical);return
        for x,y in DIR:
            j=(c+y)%12
            if (x or G[c]-G[j]==1) and not taken>>j&1:
                add(c+1,taken|1<<j,vertical|((1<<c) if x else 0))
    add(0,0,0)
    return tuple(result)


def cuts(tile,z):
    def d(c):
        return tile[(z+G[c])%12,c]
    occ=ver=0
    for c in range(12):
        x,y=d(c)
        if x<0 or (y and G[(c+y)%12]>G[c]):
            occ|=1<<c
            if x:ver|=1<<c
    return occ,ver


EMPTY=tuple((i,0,0) for i in range(6))


@lru_cache(None)
def advance_partition(part,nxt):
    """Index differences in the longitudinal cover, not just a bank color.

    A triple is (root on frontier, relative period index, winding period).
    A same-component edge creates a cycle; allow only the first one and
    only with nonzero displacement. Its lift is an infinite path with
    trees attached, not a finite cycle.
    """
    parent=list(range(12));delta=[0]*12;period=[0]*12
    for i,(root,offset,w) in enumerate(part):
        parent[i]=root;delta[i]=offset;period[root]=w
    def find(x):
        off=0
        while parent[x]!=x:
            off+=delta[x];x=parent[x]
        return x,off
    def link(i,j,shift):
        a,x=find(i);b,y=find(j)
        if a==b:
            v=abs(x+shift-y)
            if period[a] or not v:return False
            period[a]=v
        else:
            if period[a] and period[b]:return False
            parent[b]=a;delta[b]=x+shift-y
            period[a]=period[a] or period[b]
        return True
    for i in range(6):
        c=2*i
        if nxt>>c&1 and not link(i,i+6,0):return None
        for step in (-1,1):
            j=i+step
            if G[c]-G[(2*j)%12]==2 and nxt>>((c+step)%12)&1:
                if not link(i,j%6+6,j//6):return None
    reps={};out=[]
    for j in range(6,12):
        a,x=find(j)
        root,y=reps.setdefault(a,(j-6,x))
        w=period[a]
        out.append((root,(x-y)%w if w else x-y,w))
    return tuple(out)


def degree_cost(prev,nxt):
    loss=0
    for c in range(0,12,2):
        deg=(prev>>c&1)+(nxt>>c&1)
        for j in ((c-1)%12,(c+1)%12):
            mask=prev if G[j]>G[c] else nxt
            deg+=mask>>j&1
        assert deg
        if deg<4:loss+=deg-1
    return loss


def data(tile,z):
    occ,v=cuts(tile,z)
    nxt=sum((tile[(z-1+G[c])%12,c][1]==0)<<c for c in range(12))^0xaaa
    return occ,v,nxt,z%12


def initial(tile):
    p=EMPTY
    for z in range(-24,0,2):
        p=advance_partition(p,data(tile,z+2)[2]);assert p
        if z==-14:checkpoint=p
    assert p==checkpoint
    return (*data(tile,0),p)


def controls(tiles):
    # Shape and cut labels independently evaluated from the actual domino
    # directions must recur after a complete wave, including the partition.
    positive=0
    for tile in tiles.values():
        occ,inc,prev,z,p=initial(tile)
        p0=p
        for z in range(0,12,2):
            n,w,nxt,_=data(tile,z+2)
            o,v=cuts(tile,z+1)
            assert (o,v) in moves(occ) and (n,w) in moves(o)
            assert ((v|w)^0xaaa)==nxt and degree_cost(prev,nxt)==0
            p=advance_partition(p,nxt)
            assert p is not None
            positive+=1;occ,prev=n,nxt
        assert p==p0
    print("positive controls: 96 homogeneous connectivity closures,",positive,"two-slice replays")


def closure(start):
    seen={start};q=deque([start])
    while q:
        occ,inc,prev,z,p=q.popleft()
        for o,v in moves(occ):
            for n,w in moves(o):
                # v records vertical departures to the odd slice; vertical
                # arrivals there have the same column.
                nxt=(v|w)^0xaaa
                if degree_cost(prev,nxt):continue
                pp=advance_partition(p,nxt)
                if pp is None:continue
                s=n,w,nxt,(z+2)%12,pp
                if s not in seen:
                    seen.add(s);q.append(s)
        assert len(seen)<1000000,"state cutoff: inconclusive"
    return seen


def census():
    cases=[];sources=set()
    for res in range(2):
        rows=arbitrary_arms(budgets(6,res),res)
        for h in (0,1,2):
            pairs=[]
            for i,_,a in rows:
                for j,_,b in rows:
                    # h/2 is the normalized mean depth of the seam.
                    slack=12-2*(a[0]+b[2])-h*(a[1]+a[3])-(2-h)*(b[1]+b[3])
                    if slack>=0:
                        assert slack==0 and i%2==j%2==0 and i//32!=j//32
                        pairs.append((i,j));sources.add(i)
            cases.append((res,h,pairs))
    tiles={i:d for i,d,c in rows}
    controls(tiles)
    starts={i:initial(d) for i,d in tiles.items()}
    exits={}
    for i in sources:
        states=closure(starts[i])
        # Favor the construction: any partition matching the destination
        # cut is allowed. Exact destination partition is not necessary.
        exits[i]={s[:4] for s in states}
        assert starts[i] in states
        for z in range(0,12,2):
            assert data(tiles[i],z) in exits[i]
    print("zero-loss source searches",len(sources))
    for res,h,pairs in cases:
        print("parity",res,"mean depth",h/2,"zero-loss pairs",len(pairs),"survivors",
              [(i,j) for i,j in pairs if data(tiles[j],0) in exits[i]])


if __name__=="__main__":census()
