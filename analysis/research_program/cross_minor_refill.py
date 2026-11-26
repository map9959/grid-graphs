"""Price cross compression after restoring compatible marks in the physical forest."""
from .cross_minor_price import repair,verify
from .reflected_pitch_rank import ledger


def refill(rows,allowed=None,candidates=False,order=None):
    n=len(rows);nn=n*n
    marks=[c=='#' for row in rows for c in row]
    parent=list(range(nn));single=[];rest=[]
    def root(v):
        while v!=parent[v]:parent[v]=parent[parent[v]];v=parent[v]
        return v
    def neighbors(v):
        return ([v-1] if v%n else [])+([v+1] if v%n<n-1 else [])+(
                [v-n] if v>=n else [])+([v+n] if v<nn-n else [])
    for v in range(nn):
        for u in neighbors(v):
            if u<v and (marks[v] or marks[u]):
                a,b=root(u),root(v);assert a!=b;parent[a]=b
    feasible=set()
    for v in range(nn):
        if marks[v]:continue
        if allowed is not None and v not in allowed:continue
        need=[u for u in neighbors(v) if not marks[u]]
        ids=[root(u) for u in [v,*need]]
        if len(set(ids))!=len(ids):continue
        feasible.add(v)
        (single if len(need)<=1 else rest).append((len(need),v))
    if candidates:return feasible
    gain=[]
    for group in (single,sorted(rest,key=lambda t:(t[0],order(t[1]) if order else t[1]))):
        added=0
        for _,v in group:
            need=[u for u in neighbors(v) if not marks[u]]
            ids=[root(u) for u in [v,*need]]
            if len(set(ids))!=len(ids):continue
            for b in ids[1:]:parent[b]=ids[0]
            marks[v]=True;added+=1
        gain.append(added)
    return [''.join('#' if z else '.' for z in marks[i:i+n]) for i in range(0,nn,n)],gain


def shell_control(n):
    from .wired_crop_exchange import ring
    from random import Random
    assert n%6==1
    shell=set()
    for t in range(0,(n-11)//2,3):
        h=n-2*t
        holes={(0,1),(0,2),(1,h-1),(h-1,h-2),(h-2,0)}
        shell.update((t+i,t+j) for i,j in ring(h) if (i,j) not in holes)
    rows=[''.join('#' if (i,j) in shell else '.' for j in range(n)) for i in range(n)]
    priority=list(range(n*n));Random(0).shuffle(priority)
    return refill(rows,order=priority.__getitem__)[0]


def wrap(core,extra_gap=False):
    from .wired_crop_exchange import ring
    n=len(core)+6
    # Corner omissions avoid a diagonal pair. Put the only missing
    # perimeter bond across the cut for the more demanding replay.
    holes={(0,1),(1,n-1),(n-1,n-2),(n-2,0)}
    holes.update({(0,52),(0,53)} if extra_gap else {(0,2)})
    rim=set(ring(n))-holes
    return [''.join('#' if (i,j) in rim else core[i-3][j-3]
                    if 3<=i<n-3 and 3<=j<n-3 else '.' for j in range(n)) for i in range(n)]


if __name__=='__main__':
    rows=shell_control(103)
    pitch='#..'*34+'#'
    assert pitch not in rows and tuple(pitch) not in zip(*rows)
    assert not refill(rows,candidates=True)
    src=verify(rows)
    assert src[0]==src[-1]==3602
    y,x=37,49
    rr,rank,paid=repair(rows,y,x)
    sites=refill(rr,candidates=True)
    def bank_price(group):
        target=[list(r) for r in rr]
        for v in group:
            a,b=divmod(v,len(rr));target[a][b]='#'
        # Every rejected new edge touches exactly one proposed mark.
        return len(group)-ledger(target)[0]
    banks=[{v for v in sites if (v//102+2*(v%102))%5==t} for t in range(5)]
    prices=[(len(s),bank_price(s)) for s in banks]
    assert prices[1]==(12,11)
    bulk,g=refill(rr,banks[1]);assert sum(g)>=11
    print('five refill banks (size, guaranteed gain):',prices,'bank 1 tree',verify(bulk))
    out,gain=refill(rr);dst=verify(out)
    loss=src[0]-dst[0];assert loss==74
    print('saturated no-pitch source:',src,'rank',rank,'paid',paid,'regained',gain,
          'tree',dst,'net loss',loss)
    for extra_gap in (False,True):
        larger=wrap(rows,extra_gap);t=verify(larger)
        # Cut inherits its coordinates shifted by the three-site backing.
        i,j=y+3,x+3
        reduced=[list(r[:j]+r[j+1:]) for h,r in enumerate(larger) if h!=i]
        for h,r in enumerate(out):reduced[h+3][3:-3]=r
        if extra_gap:reduced[0][j-1]='.'   # keep a missing bond at the surviving hole
        dst=verify([''.join(r) for r in reduced])
        assert t[0]-dst[0]<=loss+4
        print('side 109, gap at cut',extra_gap,'loss',t[0]-dst[0],'tree',dst)
