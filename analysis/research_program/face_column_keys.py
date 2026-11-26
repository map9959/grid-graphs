"""Numeric keys ordered like the tuples used by the physical orbit chart."""
from .rank44_faces import labels, parts
from .patch_square import trans, SYM
from .four_square import masks4


def pack(xs):
    v = 0
    for x in xs:
        assert 0 <= x < 32
        v = 32*v+x
    return v


def state(s):
    m, a, hit = s
    return (('pre', 'on', 'gap', 'p0', 'p1').index(m)*9 +
            (0 if a is None else 1+4*a[0]+2*a[1]+a[2]))*2+hit


def descriptors(n, names, obj):
    def fine(i,j,S,h):
        clip = lambda z: max(-9,min(9,z))
        return *labels(i,j,S,h),clip(i-j),clip(i+j+1-S)

    positions = {}
    for S,h,finepos in [(n,8,True),(n-2,7,True),(n-3,2,False)]:
        pos = lambda i,j: fine(i,j,S,h) if finepos else labels(i,j,S,h)
        positions[S] = {pos(i,j): tuple(pos(*trans(i,j,S,g)) for g in range(8))
                        for i in range(S) for j in range(S)}
    seen = set()
    for name,x in names.items():
        kind = name[0]
        if kind == 's':
            p,f,nb,o = name[1]
            ps = positions[n][p]
            def view(g):
                rot = lambda t: ((2-t if g&4 else t)+g)%4
                v = [0]*4
                for i,z in enumerate(nb): v[rot(i)] = z
                return ps[g],tuple(v),rot(o) if o>=0 else -1
            orbit = {view(g) for g in range(8)}
            assert min(orbit)==(p,nb,o)
            k = 8*pack([*p[:2],p[2]+9,p[3]+9,*nb,o+1])+f
        elif kind == 'rankFace':
            p,m,q = name[1]
            orbit = set(zip(positions[n-3][p],masks4()[m][1],
                            [parts(q,g) for g in range(8)]))
            assert min(orbit)==(p,m,q)
            k = 8*((pack(p)*65536+m)*256+sum(z*4**(3-i) for i,z in enumerate(q)))+2
        elif kind == 'floorLine':
            _,y,(prev,p,s,u) = name
            k = 8*((pack([y,0 if prev is None else prev+1,p])*90+state(s))*90+state(u))+3
            orbit = {0}
        elif kind == 'p':
            p,m = name[1]
            orbit = set(zip(positions[n-2][p],SYM[m]))
            k = 8*(pack([*p[:2],p[2]+9,p[3]+9])*512+m)+4
        else:
            assert kind=='complete'
            k = 8*name[1]+5
            orbit = {0}
        assert k not in seen and 8%len(orbit)==0
        seen.add(k)
        assert obj.get(x,0)==(len(orbit) if k%8==1 else 0)
        yield k, (8//len(orbit) if kind not in ('floorLine','complete') else 1)
