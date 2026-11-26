"""Discharge asymmetric crossed-sector tuples through their shared directed-seam budget."""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
import subprocess
from .crossed_orbits import census
from .period_nine import state


def surviving(rows,mat,opts,f):
    ns=0
    counts=Counter()
    for t,b in product(opts[0],opts[2]):
        g=2*(rows[t][2][0]+rows[b][2][2])
        if g>18:continue
        sides=[]
        for s in (3,1):
            vals=defaultdict(list)
            for i in opts[s]:
                w=2*rows[i][2][s]+mat[int(s==1)][t][i]+mat[int(s==3)][i][b]
                if g+w<=18:vals[w].append(i)
            sides.append(vals)
        for x,ls in sides[0].items():
            for y,rs in sides[1].items():
                if x+y+g>18:continue
                ns+=len(ls)*len(rs)
                counts[x+y+g]+=len(ls)*len(rs)
                if f:
                    for i in ls:f(0,t,i);f(1,i,b)
                    for i in rs:f(1,t,i);f(0,i,b)
    return ns,dict(sorted(counts.items()))


def minimum(rows,mat,opts):
    best=(10**6,None)
    for t,b in product(opts[0],opts[2]):
        g=2*(rows[t][2][0]+rows[b][2][2])
        if g>=best[0]:continue
        h=min((2*rows[i][2][1]+mat[1][t][i]+mat[0][i][b],i) for i in opts[1])
        l=min((2*rows[i][2][3]+mat[0][t][i]+mat[1][i][b],i) for i in opts[3])
        best=min(best,(g+h[0]+l[0],(t,h[1],b,l[1])))
    return best


def test(r=0,cap=4,verify_residues=True,depth=0):
    rows,mat,opts,tr,refl=census(r,True)
    def deep(rr,residue):
        from .period_nine import arm,profile
        if not depth:return rr
        ret=[]
        for i,d,c in rr:
            nc=[]
            for side in ('top','right','bottom','left'):
                if depth<=8:
                    pf=profile(d,depth,side,8+6*residue,18)
                    nc.append(1000 if sum((-1)**j for j,(p,_) in enumerate(pf) if p) else arm(depth,pf))
                else:
                    from .deep_arms import lower_bound
                    nc.append(lower_bound(d,depth,side,8+6*residue))
            ret.append((i,d,nc))
        print("depth",depth,"old/new arm costs",dict(Counter((x,y) for (_,_,c),(_,_,e) in zip(rr,ret) for x,y in zip(c,e))),flush=True)
        return ret
    rows=deep(rows,r)
    opts=[[i for i,d,c in rows if c[s]<=9] for s in range(4)]
    @lru_cache(None)
    def orbit(i,j):
        return min(zip(tr[i],tr[j]))
    active=set()
    n,_=surviving(rows,mat,opts,lambda d,i,j:active.add((d,i,j)))
    def name(d,i,j):
        return orbit(refl[i],refl[j]) if d else orbit(i,j)
    keys={name(*e) for e in active if mat[e[0]][e[1]][e[2]]<=cap}
    lo=[state(d) for _,d,_ in rows]
    hi=[state(d,True) for _,d,_ in rows]
    # Translate each half independently into a canonical background for
    # its distance table. At lookup restore relative column and phase.
    # tr[i][9*a+b] samples i at (row+2a,col+2b).
    rep=[min(t) for t in tr]
    shifts=[divmod(t.index(min(t)),9) for t in tr]
    print("tuples",n,"active directed entries",len(active),"queries",len(keys),
          "sector sizes",dict(Counter(lo[i][0].bit_count() for i,j in keys)),flush=True)
    if cap<0:return
    binary=Path(__file__).resolve().parents[2]/'target/release/diagonal_nine'
    exact={}
    for occ in sorted({lo[i][0].bit_count() for i,j in keys}):
        jobs=sorted((i,j) for i,j in keys if lo[i][0].bit_count()==occ)
        def line(i,j):
            ai,bi=shifts[i];aj,bj=shifts[j]
            return " ".join(map(str,[*lo[rep[i]],*hi[rep[j]],cap,i,j,
                                     (2*(bi-bj))%18,(ai-bi-aj+bj)%9]))
        lines=[line(i,j) for i,j in jobs]
        out=subprocess.run([binary,"--sector"],input="\n".join(lines),text=True,capture_output=True,check=True)
        for pair,line in zip(jobs,out.stdout.splitlines(),strict=True):
            i,j,v=map(int,line.split());assert pair==(i,j)
            exact[pair]=min(cap+1,v)
        print("completed occupancy",occ,"queries",len(jobs),flush=True)
    for d,i,j in active:
        v=exact.get(name(d,i,j),0)
        if v<=cap and name(d,i,j) in exact:assert v>=mat[d][i][j]
        mat[d][i][j]=max(mat[d][i][j],v)
    print("directed minima (cap+1 means strictly over cap)",dict(Counter(exact.values())),flush=True)
    print("final survivors:",surviving(rows,mat,opts,None),"matrix lower bound",minimum(rows,mat,opts),flush=True)
    if verify_residues:
        for residue in range(3):
            if residue==r:continue
            rr,mm,oo,tt,rf=census(residue,True)
            rr=deep(rr,residue)
            oo=[[i for i,d,c in rr if c[s]<=9] for s in range(4)]
            assert tt==tr
            extra=set()
            def apply(d,i,j):
                pair=orbit(rf[i],rf[j]) if d else orbit(i,j)
                if mm[d][i][j]<=cap and pair not in exact:
                    extra.add(pair)
                return d,i,j,pair
            # Do not mutate the matrix until the original survivors have
            # all contributed their required queries.
            entries=set()
            surviving(rr,mm,oo,lambda d,i,j:entries.add(apply(d,i,j)))
            for d,i,j,pair in entries:mm[d][i][j]=max(mm[d][i][j],exact.get(pair,0))
            print("residue",residue,"missing queries",len(extra),"survivors",surviving(rr,mm,oo,None),
                  "matrix lower bound",minimum(rr,mm,oo),flush=True)


if __name__=="__main__":
    import sys
    test(*(map(int,sys.argv[1:])))
