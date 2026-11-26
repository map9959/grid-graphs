"""Sparse GF(2) witness against an even number of half defects.

Use actual oriented local occurrences; no probability or LP solution is
assumed. Project each bond, incidence and overlap onto the physical anchor
and event. The bits of a separating row combination are back-substituted
from a GF(2) echelon basis, with both RHS parities checked explicitly.
"""
from collections import Counter
from itertools import product

from .square_dual_physical import DIR, MASKS, SYM, inspect, trans
from .square_current import states


def axis(s, d, i, p=6):
    return i if i<d else 2*d+p+i-s if i>=s-d else d+(i-d)%p


def cells(n,depth):
    for t in (0,1):
        s=n-2*t
        d=depth+3-t
        for i,j in product(range(s),repeat=2):
            if all(not d+6<=v<s-d for v in (i,j)):
                yield t,s,i,j


def model(n,depth,family):
    def loc(s,d,i,j):return axis(s,d,i)*32+axis(s,d,j)
    def pack(s,d,i,j,q,event):return (loc(s,d,i,j)*9+q)*64+event
    T={}
    def key(tag): return 1<<T.setdefault(tag,len(T))
    for t,s,i,j in cells(n,depth):
        dirs=[d for d,(a,b) in enumerate(DIR) if 0<=i+a<s and 0<=j+b<s]
        gt=[trans(i,j,s,g) for g in range(8)]
        fine=[(axis(s,6-t,r,3),axis(s,6-t,c,3)) for r,c in gt]
        norm=key((t,loc(s,depth,i,j)))
        ext=tuple((q,i-a,j-b) for q,(a,b) in enumerate(product(range(3),repeat=2))
                  if t or (0<=i-a<n-2 and 0<=j-b<n-2))
        for ev in MASKS if t else states(dirs):
            if t:
                m=ev; images=SYM[m]
            else:
                f,sig=ev
                o=next((d for d in dirs if sig[d][2]==(1 if d<2 else -1)),-1)
                if (i,j)==(0,0) and o!=-1:continue
                if len(dirs)==2 and (i,j)!=(0,0) and o==-1:continue
                nb=[sig[d][int(d<2)] if d in dirs else 9 for d in range(4)];images=[]
                for g in range(8):
                    def turn(d):return ((2-d if g&4 else d)+g%4)%4
                    word=[9]*4
                    for d in range(4):word[turn(d)]=nb[d]
                    images.append((f,tuple(word),turn(o) if o>=0 else -1))
            w=family['p' if t else 's',min(zip(fine,images))]*1008
            if w not in (0,36):continue
            col=norm
            if w:col^=key((5,0))
            for d in dirs:
                a,b=DIR[d];v=i+(a if d>=2 else 0);z=j+(b if d>=2 else 0)
                if t:
                    e=sum(((m>>(3*y+x))&1)<<r for r,(y,x) in enumerate(
                        (y,x) for y,x in product(range(3),repeat=2) if 0<=y-a<3 and 0<=x-b<3))
                else:
                    u,vv,arr=sig[d];e=(u*2+vv)*3+arr+1
                col^=key((2+t,pack(s,depth,v,z,d%2,e)))
            for q,a,b in ext:
                y,x=divmod(q,3);directions=[d for d,(dr,dc) in enumerate(DIR) if 0<=y+dr<3 and 0<=x+dc<3]
                bits=[m>>q&1 if t else f]+[(m>>(q+DIR[d][0]*3+DIR[d][1]))&1 if t else nb[d] for d in directions]
                e=sum(bit<<k for k,bit in enumerate(bits))
                col^=key((4,pack(n-2,depth,i if t else a,j if t else b,q,e)))
            yield col,T


def run(depth):
    family=inspect(20);piv={}
    for z,T in model(35,depth,family):
        while z:
            i=z.bit_length()-1
            if i not in piv:
                piv[i]=z;break
            z^=piv[i]
    def rhs(n):
        z=0
        for t in (0,1):
            s=n-2*t
            for i,j in product(range(s),repeat=2):
                z^=1<<T[t,axis(s,depth,i)*32+axis(s,depth,j)]
        return z
    for n in (35,77):
        z=rhs(n);rem=[]
        while z:
            i=z.bit_length()-1
            if i in piv:z^=piv[i]
            else:rem.append(i);z^=1<<i
        print(depth,n,'codimension',len(T)-len(piv),'rhs remainder',len(rem),flush=True)
        if not rem:return
        def extract(i):
            y=1<<i
            for j in sorted(piv):
                if (y&piv[j]).bit_count()%2:y^=1<<j
            return y
        candidates=[extract(i) for i in rem]
        y=min(candidates,key=int.bit_count)
        assert (rhs(n)&y).bit_count()%2 and all((c&y).bit_count()%2==0 for c in piv.values())
        cert=sorted(tag for tag,i in T.items() if (y>>i)&1)
        print('parity support',len(cert),Counter(k for k,_ in cert),flush=True)
        yield n,cert


if __name__=='__main__':
    import sys
    import json
    from pathlib import Path
    depth=int(sys.argv[1])
    cert=dict(run(depth))
    if '--save' in sys.argv:
        assert len(cert)==2
        assert cert[35]==cert[77] and [e for e in cert[35] if e[0]<2]==[(1,429)]
        masks=Counter()
        for kind,idx in cert[35]:
            if kind>=2:masks[(kind,idx//64)] |= 1<<(idx%64)
        dest=Path(__file__).resolve().parents[2]/'lean/GridGraphs/ResidueTwoUpper/Data/exceptional.parity'
        dest.write_text(''.join(f'{k*10000+i} {v}\n' for (k,i),v in sorted(masks.items())))
