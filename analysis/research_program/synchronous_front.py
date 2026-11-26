"""A moving frontier: four tile rows south and three tile columns east.

Use the same coordinate for both occurrences of every overlap. In the
induction step three columns of the east suffix pass to the prefix.
"""
from functools import lru_cache
from .coupled_mask_check import Pool,checker
from .synchronous_grid import domains,unpack,rectangle
from .ordered_seam_price import table,rowchart

def fold(i,g,a=3):return i if i<g else max(g,i-a)

@lru_cache(None)
def cell(axis,r,j,d):
    return frozenset((a,b,c,e) for (a,c),ns in table(axis,r,j,d).items() for b,e in ns)

def prune(grid,pool,W,H,gaps,rootfrom=None,south=False,hmax=3,sealed=(),sides=3,ygaps=(),block=1):
    for _ in range(8):
        initial=grid.copy()
        for h in range(2,hmax+1):
            for turn in range(20):
                old=grid.copy()
                for hor in (True,False):
                    fs={};width=H if hor else W
                    for pos in (range(width-h+1) if turn%2==0 else reversed(range(width-h+1))):
                        if not hor and h>3 and any(pos<=g<pos+h-1 for g in gaps):continue
                        e=(2*(south and pos+h==H) if hor else (int(pos==0)+2*(pos+h==W))&sides)
                        # An exposed top side may leak. Only mark trunks
                        # already proved to meet distinct teeth as rooted.
                        rf=rootfrom if hor and pos==0 else None
                        rm=sum(1<<(3*i) for i in range(h) if not hor and
                               rootfrom is not None and pos+i>=rootfrom)
                        sm=sum(7<<(3*i) for i in range(h) if not hor and pos+i in sealed)
                        key=e,rf,rm,sm
                        if key not in fs:
                            fs[key]=checker(W if hor else H,h,hor,e,pool,
                                along=gaps if hor else ygaps,across=ygaps if hor else gaps,block=block,
                                stride=W-1,ends=sides if hor else 2*int(south),rootmask=rm,rootfrom=rf,sealed=sm)
                        if not fs[key](grid,pos):return False
                if old==grid:break
        if grid==initial:break
    return True

def base(axis,K,y0,L,gR,gy,q=1):
    # All added columns in the right plateau and all added rows below
    # the seed. Encode the entire base relation, not just sampled masks.
    ds,g=domains(axis,K,q,gR,gy)
    F=[[frozenset(unpack(p) for p in ds[g[y*(K-1)+x]]) for x in range(K-1)]
       for y in range(y0,y0+L)]
    f=max(front(F),(q if isinstance(q,int) else q[1])+1)
    for y in range(y0+1):
        for x in range(f,K-1):
            assert all(w[0]==w[2]==(7 if y else 6) for w in map(unpack,ds[g[y*(K-1)+x]]))
    return F

def front(F):
    return max((x+1 for x,s in enumerate(F[0]) if any(p[0]!=7 or p[2]!=7 for p in s)),default=0)

def attempt(axis,K=53,y0=24,L=2,gL=8,gR=38,gy=36,extra=3,steps=6,tail=False,native=False,q=1,seed_axis=None):
    test=rectangle if native else prune
    qs=(q,) if isinstance(q,int) else tuple(q)
    seeds=[base(seed_axis or axis,K,y0,L,gR,gy,v) for v in qs]
    F=[[frozenset.union(*(s[j][i] for s in seeds)) for i in range(K-1)] for j in range(L)]
    W=K+3;H=L+5+extra;f=max(front(F),max(v if isinstance(v,int) else v[1] for v in qs)+1)
    assert gL<f<gR
    pool=Pool()
    for n in range(steps):
        grid=[]
        for j in range(H-1):
            for i in range(W-1):
                p=cell(axis,rowchart(i,W),7,-4)
                if j<L:p=p&F[j][fold(i,gR)]
                grid.append(pool.intern(p))
        if not test(grid,pool,W,H,(gL,gR+3),f):
            if tail:raise AssertionError('expected an inductive handoff before testing the tail')
            print('empty induction slab');return True
        new=[x.copy() for x in F]
        for j in range(L):
            for i in range(W-1):
                x=fold(i,gL);new[j][x]=new[j][x]|pool.items[grid[(4+j)*(W-1)+i]]
        handoff=all(all(p[h]==7 for p in pool.items[grid[j*(W-1)+i]] for h in (0,1,2,3))
                    for i in range(f+3,W-1) for j in range(4))
        print('step',n,'front',f,'new front',front(new),'handoff',handoff,
              'changed',sum(x!=y for a,b in zip(new,F) for x,y in zip(a,b)),flush=True)
        if new==F:
            if not tail:return handoff
            assert handoff
            for rem in range(20,24):
                gd=[]
                for j in range(rem-1):
                    for i in range(K-1):
                        p=cell(axis,rowchart(i,K),rowchart(K-rem+j,K),-4)
                        if j<L:p=p&F[j][i]
                        gd.append(pool.intern(p))
                live=test(gd,pool,K,rem,(gL,gR),f,True)
                print('remaining rows',rem,'terminal support',live,flush=True)
                if live:return False
            return True
        F=new
        if front(F)>f:return False
    return False
if __name__=='__main__':
    import sys
    print('inductive?',attempt(*map(int,sys.argv[1:])))
