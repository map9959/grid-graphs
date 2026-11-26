"""Modular potentials for forced primal and complementary dual edges.

A simple grid cycle has nonzero signed enclosed area over the integers.
Small moduli give necessary relaxations without choosing any arrows.
"""
from itertools import product
from .odd_frames import frame

def install(f,vp,n,domains,tile,flags,d0,modulus):
    assert 2<=modulus<=11
    mark=lambda i,j:vp.id(('mark',i,j))
    for (i,j),ms in domains.items():
        for m in ms:
            for a,b in product(range(3),repeat=2):
                z=mark(1+3*i+a,1+3*j+b);f.append([-tile(i,j,m),z if m>>(3*a+b)&1 else -z])
    for u,b in frame(n,(0,1,3,3)).items():f.append([mark(*u)*(1 if b else -1)])
    if not flags:
        s=vp.id();f.append([s]);flags={d0:s}
    # Work with one origin per connected graph, never requiring an
    # absolute potential except to break its global additive symmetry.
    def field(tag,i,j):
        if tag=='D' and not (0<=i<n-1 and 0<=j<n-1):i=j=-1
        return (tag,i,j)
    seen=set()
    def add(u,v,delta,guard):
        delta%=modulus
        if modulus==2:
            a=vp.id(u);b=vp.id(v)*(-1 if delta else 1);f.extend([guard+[-a,b],guard+[a,-b]])
        else:
            for x in (u,v):
                if x not in seen:
                    seen.add(x);vs=[vp.id((*x,k)) for k in range(modulus)];f.append(vs)
                    for i in range(modulus):
                        for j in range(i):f.append([-vs[i],-vs[j]])
            for k in range(modulus):f.append(guard+[-vp.id((*u,k)),vp.id((*v,(k+delta)%modulus))])
    for i,j in product(range(n),repeat=2):
        for vertical,(a,b) in enumerate(((0,1),(1,0))):
            x,y=i+a,j+b
            if max(x,y)>=n:continue
            g=[mark(i,j),mark(x,y)];ext=flags.get(j) if vertical and i==1 else None
            # Primal: horizontal edges integrate row number, vertical zero.
            u,v=field('P',i,j),field('P',x,y)
            for z in g:add(u,v,0 if vertical else i,[-z])
            if ext:add(u,v,0,[-ext])
            # Dual: assign each primal vertex unit mass and route west
            # then north to NW. Integrate the signed crossing flux.
            left,right=(field('D',i-1,j),field('D',i,j)) if not vertical else (field('D',i,j),field('D',i,j-1))
            flow=n*(n-1-i) if vertical and j==0 else (0 if vertical else n-1-j)
            add(left,right,flow,g+([ext] if ext else []))
