"""Optimal freely chosen cap on vertical pitch-three rails, by column transfer."""
from functools import lru_cache
from .extend_forest_28 import verify


@lru_cache(None)
def transitions(h,old,part,rail,first):
    # Boundary nodes 0,1 are the contracted top and bottom components.
    # The preceding rail row has all its sites in component 0 because
    # the pitch is 3; the blank penultimate row is attached to 1.
    out=[]
    for m in range(1<<h):
        diag=((old<<1)|(old>>1))&m
        if diag:continue
        if not first and rail and old&1:continue
        p=list(part)+list(range(h+2,2*h+2))
        def rt(x):
            while x!=p[x]:x=p[x]
            return x
        def edge(a,b):
            a,b=rt(a),rt(b)
            if a==b:return False
            p[a]=b;return True
        off=h+2
        if (rail or m&1) and not edge(0,off):continue
        if m>>(h-1) and not edge(1,off+h-1):continue
        if not all(edge(off+i,off+i+1) for i in range(h-1) if (m>>i)&3):continue
        if not first and not all(edge(2+i,off+i) for i in range(h) if (m|old)>>i&1):continue
        roots=[rt(x) for x in [0,1,*range(off,off+h)]]
        out.append((m,tuple(roots.index(a) for a in roots)))
    return out


def construct(n,h):
    assert n%3==1 and h>=1
    states={(0,tuple(range(h+2))):(0,0)}
    for j in range(n):
        opts={}
        for (old,part),(v,word) in states.items():
            for m,s in transitions(h,old,part,j%3==0,j==0):
                z=v+m.bit_count()
                if z>opts.get((m,s),(-1,0))[0]:opts[m,s]=z,(word<<h)|m
        states=opts
    z,word=max(states.values())
    cap=[''.join('#' if word>>(h*(n-1-j)+i)&1 else '.' for j in range(n)) for i in range(h)]
    rows=['#'*n,'.'*n]+[('#..'*(n//3))+'#']*(n-h-4)+cap+['.'*n,'#'*n]
    return rows


def certify_period():
    # Same transition as construction, retaining only the maximum scores.
    h=4;states={(0,tuple(range(h+2))):0};base=None
    for j in range(40):
        q={}
        for (old,part),value in states.items():
            for m,s in transitions(h,old,part,j%3==0,j==0):
                q[m,s]=max(q.get((m,s),-1),value+m.bit_count())
        states=q
        if j%3 or j<9:continue
        k=j//3
        if k==3:base=states
        assert max(states.values())==3*k+5+(3*k-13)//10
    assert states=={key:v+33 for key,v in base.items()}
    print('10 -> 40 columns: identical',len(states),'reachable states; every maximum increases by 33')
    print('10 base residues checked; lower score = 3k^2+5k+floor((3k-13)/10), k>=3')


if __name__=='__main__':
    import sys
    if '--period' in sys.argv:certify_period()
    else:
        n,h=map(int,sys.argv[1:])
        rows=construct(n,h)
        print('side',n,'cap height',h,'verified',verify(rows),flush=True)
        print('\n'.join(rows[-h-2:]))
