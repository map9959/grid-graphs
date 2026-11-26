"""Propose three physical, single-view price tables for Lean to check.

Orbit averaging happens only during proposal. Soundness works for *any*
three tables, including rounded or incorrectly exported prices.
"""
import json
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from .patch_square import relaxation, signature, DIR, trans

HERE = Path(__file__).resolve().parent
DEST = HERE.parents[1]/'lean/GridGraphs/FiniteOne/Data'


def proposal(n, leaf=None, multipliers=None):
    tags = []
    pooled = n == 55
    source = HERE / (f'diagonal_d4_w4_{n}.json' if pooled else f'patch_square_{n}_dual.json')
    names,rows,obj = relaxation(n, 8 if pooled else None, pooled=4 if pooled else None,
                                period=3 if pooled else 1, diagonal=4 if pooled else None, tags=tags)
    if multipliers is not None:
        ys = [(i,Fraction(v,1000000)) for i,v in multipliers if i<len(rows)]
    elif n == 16:
        from .side28_score import solve
        optimum,ys,_ = solve([(cs,o) for cs,o,_ in rows],[b for _,_,b in rows],obj,names,interior='cross')
        print('side 16 LP optimum',optimum,flush=True)
        ys = [(i,Fraction(v).limit_denominator(1000000)) for i,v in enumerate(ys) if abs(v)>1e-9]
    else:
        data = json.loads(source.read_text())
        if not pooled:
            assert signature(rows,obj)==data['model']
        ys = [(int(i),Fraction(v)) for i,v in (data.items() if pooled else data['multipliers'])]
    prices = {}
    unit = 100000
    for i,y in ys:
        sign,tag = tags[i]
        if tag[0] in ('s','sp','pp'):
            prices[tag] = round(y*sign*unit)
    del names,rows,obj,tags

    def pos(p,s):
        if not pooled:
            return p
        x,y=p
        def axis(v):return v if v<4 else 11+v-s if v>=s-4 else 4+(v-4)%3
        def clip(v):return max(-4,min(4,v))
        return axis(x),axis(y),clip(x-y),clip(x+y+1-s)

    @lru_cache(None)
    def mapping(fam,d,g):
        z = ((6-d if g>=4 else d)+g)%4 if fam!='sp' else None
        if fam=='s':
            keys=[(a,b,sign) for a in range(2) for b in range(2) for sign in [-1,0,1]]
            return z,[(b,a,-s) if z>=2 else (a,b,s) for a,b,s in keys]
        def cells(a):
            if fam=='sp':
                x,y=divmod(a,3)
                return [(x,y)]+[(x+i,y+j) for i,j in DIR if 0<=x+i<3 and 0<=y+j<3]
            u,v=DIR[a]
            return [(i,j) for i in range(3) for j in range(3) if 0<=i-u<3 and 0<=j-v<3]
        if fam=='sp':
            a,b=trans(*divmod(d,3),3,g);z=3*a+b
        old=[trans(*p,3,g) for p in cells(d)]
        order=[old.index(p) for p in cells(z)]
        return z,[tuple((m>>j)&1 for j in order) for m in range(1<<len(order))]

    ids={};seq=[];tables=[]
    for fam,side,ds in [('s',n,2),('pp',n-2,2),('sp',n-2,9)]:
        for x in range(side):
            for y in range(side):
                for d in range(ds):
                    u,v=divmod(d,3) if fam=='sp' else DIR[d]
                    if fam!='sp' and (x+u>=side or y+v>=side):
                        seq.append(0);continue
                    vec=[0]*len(mapping(fam,d,0)[1])
                    for g in range(8):
                        p=pos(trans(x,y,side,g),side)
                        s=n if fam=='sp' else side
                        q=pos(trans(x+u,y+v,s,g),s)
                        z,keys=mapping(fam,d,g)
                        neg=fam!='sp' and z>=2
                        args=(fam,q,p,z-2) if neg else (fam,p,q,z)
                        if fam=='pp':args=(*args[:3],*DIR[z%2])
                        for j,key in enumerate(keys):
                            vec[j]+=(-1 if neg else 1)*prices.get((*args,key),0)
                    sparse=tuple((j,v) for j,v in enumerate(vec) if v)
                    if not sparse:seq.append(0);continue
                    if sparse not in ids:
                        ids[sparse]=len(tables)+1;tables.append(sparse)
                    seq.append(ids[sparse])
    # Printable varints: sparse word tables followed by dense table indices.
    out=bytearray()
    def put(v):
        while v>=32:out.append(80+v%32);v//=32
        out.append(48+v)
    put(8*unit);put(len(tables))
    for row in tables:
        put(len(row))
        for j,v in row:put(j);put(2*v if v>=0 else -2*v-1)
    for i in seq:put(i)
    DEST.mkdir(parents=True,exist_ok=True)
    (DEST/f's{n}{leaf or ""}.v32').write_bytes(out+b'\n')
    print(n,len(tables),len(out),flush=True)


if __name__=='__main__':
    import sys
    for arg in sys.argv[1:]:proposal(int(arg))
