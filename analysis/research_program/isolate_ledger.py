"""Constant-radius isolate test: no board CNF, no orientation search."""
from itertools import product
from functools import lru_cache
from collections import Counter
from .defect_window import table,DIR
from .odd_frames import frame

def physical(rows):
    """Check the two color equations directly, without orientation variables."""
    n=len(rows);pts=list(product(range(n),repeat=2));X={u for u in pts if rows[u[0]][u[1]]=='#'}
    c=lambda u:sum(u)%2
    M=Counter(map(c,X));N=Counter(map(c,pts));B=Counter();I=Counter();J=Counter();adj=0
    for i,j in pts:
        nb=[(i+a,j+b) for a,b in DIR if 0<=i+a<n and 0<=j+b<n]
        m=sum(v in X for v in nb)
        if (i,j) in X:
            B[c((i,j))]+=4-len(nb);adj+=m
        else:
            assert m<=2
            if m==0:I[c((i,j))]+=1
            if m==2:J[c((i,j))]+=1
    r=len(X)-adj//2
    for t in (0,1):assert J[1-t]-I[1-t]==3*M[t]+r-B[t]-N[1-t]
    return len(X),r,[I[t] for t in (0,1)],[J[t] for t in (0,1)]

offsets=list(product(range(-1,2),repeat=2))
def run(n):
    T,P,S=table(n);frames=[w for w in product(range(4),repeat=4)
                            if sum(v in (0,2) for v in w) in (1,2)]
    @lru_cache(None)
    def extensions(m,domain,fixed,tabs):
        core={u for d,u in enumerate(offsets) if m>>d&1}
        known=dict(fixed)
        if any(int(u in core)!=known[u] for u in offsets if u in known):return False
        states=[core]
        for r,c in domain:
            if (r,c) in offsets:continue
            two=[X|{(r,c)} for X in states if not any((r+a,c+b) in X for a,b in product((-1,1),repeat=2))] if known.get((r,c))!=0 else []
            states=(states if known.get((r,c))!=1 else [])+two
        for X in states:
            if all(P(t)[sum(((r+a,c+b) in X)<<(3*a+b) for a,b in product(range(3),repeat=2))]==0
                   for r,c,t in tabs):return True
        return False
    # Test all geometric types, including the reflected ends. Every site
    # farther than 8 from an end has a phase-only radius-two neighborhood.
    axis=sorted(set(range(9))|set(range(12,15))|set(range(n-9,n)))
    locations=[]
    for i,j in product(axis,repeat=2):
        if min(i,j,n-1-i,n-1-j)==0:continue
        q=S(T(0,i,j),(0,1,2,3),-1,False,False)[0]
        if q not in (0,72):continue
        ms=[m for m,z in enumerate(P(T(1,i-1,j-1))) if z==0 and m&186==0]
        if not ms:continue
        dom=tuple((r,c) for r,c in product(range(-2,3),repeat=2) if 0<=i+r<n and 0<=j+c<n)
        tabs=tuple((r,c,T(1,i+r,j+c)) for r,c in product(range(-2,1),repeat=2)
                   if (r,c) in dom and (r+2,c+2) in dom)
        locations.append((i,j,q,ms,dom,tabs))
    counts=Counter();summary={}
    for w in frames:
        f=frame(n,w);possible=[]
        for i,j,q,ms,dom,tabs in locations:
            fixed=tuple(((r,c),f[i+r,j+c]) for r,c in dom if (i+r,j+c) in f)
            if any(extensions(m,dom,fixed,tabs) for m in ms):possible.append((i,j,q))
        assert all(min(i,j,n-1-i,n-1-j)==2 and q==72 for i,j,q in possible)
        summary[w]=possible
        counts[sum(v in (0,2) for v in w),tuple(sorted(set((min(i,j,n-1-i,n-1-j),q) for i,j,q in possible)))]+=1
    print('representative isolate types (gap count, (depth,center charge)); frame counts:',counts)
    # The first four inward distances around each corner have already
    # been excluded for the single star. At every later eligible distance
    # the inward neighbor of the boundary (row one) is known empty.
    for ell in range(5,n-5,3):
        ds=(0,1,2,3);t=T(0,2,ell)
        charged={(out,m) for out in (-1,*ds)
                 for m,q in enumerate(S(t,ds,out,False,False)) if not m&16 and q==72}
        assert charged=={(-1,0)}
    # Verify saturation of the sampled center/halo types, including
    # relative coordinates at both ends and the frame's two outer rings.
    ax=lambda x,L,h:x if x<h else 2*h+3+x-L if x>=L-h else h+(x-h)%3
    def key(x):
        return (min(x,4),min(n-1-x,4),
                tuple(ax(x+d,n-t*2,6-t) if 0<=x+d<n-t*2 else -1
                      for t in (0,1) for d in range(-2,3)))
    assert {key(x) for x in axis}=={key(x) for x in range(n)}
    print('all axis halo types covered; 72-star at eligible depth-two sites = empty cross, no arrow')
    k=(n-2)//3;M=3*k*k+7*k-(k-5)//7
    for g in (1,2):
        I=2-g;B=4*n-4-g;r=n*n-1-I+B-3*M
        assert r==8*n//7-2
        print(f'upper-target ledger: n={n} gaps={g} isolates={I} runs={r} run joins={r-1}')
    from .zipper_rails import build
    if n>=119:print('rail replay (score, runs, isolates by color, joins by color):',physical(build(n)))
    return summary
if __name__=='__main__':
    import sys
    run(int(sys.argv[1]) if len(sys.argv)>1 else 35)
