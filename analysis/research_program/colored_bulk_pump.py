"""Exact endpoint relation of two-tile-high tracks retaining grounded colors."""
from itertools import product
from .tile_circulation import enumerate_blocks

def edges(B,axis,colors=2,eligible=(True,)*4,rootline=None):
    graph=set()
    for w in B:
        if any(allow and m&16 and m&(40 if axis==1 else 130) for allow,m in zip(eligible,w)):continue
        X={(i,j) for i,j in product(range(3*(len(w)//2)),range(6)) if w[2*(i//3)+j//3]>>(3*(i%3)+j%3)&1}
        # Forced paths among marks decompose into hops of length one or
        # two. A two-edge route via an unmarked site is still forced.
        par={u:u for u in X}
        def rt(u):
            while par[u]!=u:u=par[u]
            return u
        for u in X:
            for v in X:
                if abs(u[0]-v[0])+abs(u[1]-v[1])<=2:par[rt(u)]=rt(v)
        rs=sorted({rt(u) for u in X});ids={r:i for i,r in enumerate(rs)}
        pinned={ids[rt(u)] for u in X if u[0]==rootline}
        for color in product(range(colors),repeat=len(rs)):
            if any(color[h] for h in pinned):continue
            ends=[]
            for side in (0,1):
                mask=sum(color[ids[rt((i,j))]]<<((colors-1).bit_length()*(3*i+j%3)) for i,j in X if j//3==side)
                ends.append((*w[side::2],mask))
            graph.add(tuple(ends))
    return graph

def powers(g,orbits=False):
    nodes=sorted({v for e in g for v in e});ix={v:i for i,v in enumerate(nodes)}
    if orbits:
        # Simultaneous renaming of the four colors does not change an
        # edge. Test every exit, and one representative of every entrance
        # orbit. Propagate these entrance bitsets FORWARD down the graph.
        def canonical(u):
            marks=[3*(3*i+a)+b for i,m in enumerate(u[:-1]) for a,b in product(range(3),repeat=2) if m>>(3*a+b)&1]
            rename={};return tuple(u[:-1])+(sum(rename.setdefault((u[-1]>>(2*k))&3,len(rename))<<(2*k) for k in marks),)
        reps={canonical(u) for u in nodes};assert reps<=set(nodes);indices={u:i for i,u in enumerate(sorted(reps))}
        prev=[1<<indices[u] if u in indices else 0 for u in nodes]
    else:prev=[1<<i for i in range(len(nodes))]
    adj=[[] for _ in nodes]
    for a,b in g:
        if orbits:adj[ix[b]].append(ix[a])
        else:adj[ix[a]].append(ix[b])
    history=[prev];sizes=[]
    for length in range(1,90):
        new=[]
        for vs in adj:
            x=0
            for v in vs:x|=prev[v]
            new.append(x)
        if length>=14 and new==history[length-14]:
            s=length-14
            return len(nodes),len(g),s,length,sum(v.bit_count() for v in new)
        history.append(new);prev=new
    raise AssertionError('14-step relation did not repeat within search range')
def test(axis,colors=2):
    assert colors in (2,4)
    g=edges(enumerate_blocks(0),axis,colors)
    print('axis',axis,colors,'colors: states, edges, equal lengths, reachable pairs:',powers(g))

def triple(axis):
    from collections import defaultdict
    B=enumerate_blocks(0);nexts=defaultdict(list)
    for b in B:nexts[b[:2]].append(b[2:])
    wide=[b+c for b in B for c in nexts[b[2:]]]
    g=edges(wide,axis,4,eligible=(True,)*6)
    print('three jointly filled tile rows, four colors; states, edges, equal lengths, canonical pairs:',powers(g,True))

def flat(axis,vertical=False):
    from .tile_family_lp import projected,typ
    B=projected(3,5);k=39;K=k-1
    reps={typ(i,K):i for i in range(K)}
    ans=[]
    for u,i in sorted(reps.items()):
        ok=tuple(min(2+3*(i+h),116-3*(i+h))>=14 for h,j in product(range(2),repeat=2))
        root=1 if i==0 else 4 if i==K-1 else None
        # Middle along-axis types never contain the distance-five star.
        words=B[u,6]
        effective=axis
        if vertical:
            def transpose(m):return sum((m>>(3*r+c)&1)<<(3*c+r) for r,c in product(range(3),repeat=2))
            words=[tuple(transpose(w[h]) for h in (0,2,1,3)) for w in B[6,u]]
            effective=3-axis
        g=edges(words,effective,4,ok,root);info=powers(g);ans.append(info[2])
        print('transverse type',u,'equal lengths',info[2:4],'states',info[0],flush=True)
    print('common',('vertical' if vertical else 'horizontal'),'42-site shortening threshold (tile steps)',max(ans))
if __name__=='__main__':
    import sys
    if '--triple' in sys.argv:triple(int(sys.argv[1]))
    elif '--flat' in sys.argv:flat(int(sys.argv[1]),'--vertical' in sys.argv)
    else:test(*map(int,sys.argv[1:]))
