"""Folded square with one common insertion count on both axes.

Use mark-quadruple occupation masses of the *same physical cells* on the
two scans. The signed certificate is checked with integer arithmetic.
"""
from array import array
from collections import defaultdict
from subprocess import run
from .coupled_mask_grid import instance

def domains(axis,k,q,gx,gy):
    s=run(['target/coupled_mask_grid','3',f'--gx={gx}',f'--gy={gy}','--rounds=12','--emit'],
          input=instance(axis,k,q),text=True,capture_output=True,check=True).stdout
    assert s.splitlines()[-1]=='OPEN (joint strip fixed point)'
    ds,g=s.split('DOMAINS\n')[1].split('GRID\n');ds=[tuple(map(int,l.split())) for l in ds.splitlines()]
    return ds,list(map(int,g.splitlines()[0].split()))

def setup(axis,k,q,gx,gy,hard=False):
    import numpy as np
    import highspy as hp
    ds,g=domains(axis,k,q,gx,gy)
    # Each edge has (table label, source, destination, extra). A loop
    # is traversed L times, the mandatory edge once. L=14t.
    def edges(gap):return [(i,i,i+1,0) for i in range(k-1)]+[(gap,gap,gap,1)]
    ex=edges(gx);ey=edges(gy);groups=[];index={};prices=array('i');signed=array('i')
    def idx(key):
        if key not in index:index[key]=len(index)+1
        return index[key]
    for Y,(j,u,v,h) in enumerate(ey):
        for X,(i,l,r,w) in enumerate(ex):
            begin=len(prices)
            for atom in ds[g[j*(k-1)+i]]:
                a,b,c,d=[(atom>>z)&511 for z in (0,9,18,27)]
                # Count the upper-left tile at each physical plaquette
                # and complete the last row and column at the true ends.
                cost=3-a.bit_count()
                if r==k-1:cost+=3-c.bit_count()
                if v==k-1:cost+=3-b.bit_count()
                if r==v==k-1:cost+=3-d.bit_count()
                prices.append(cost)
                signed.extend((idx((0,X,u,a,c)) if u else 0,-idx((0,X,v,b,d)) if v<k-1 else 0,
                               idx((1,Y,l,a,b)) if l else 0,-idx((1,Y,r,c,d)) if r<k-1 else 0))
            groups.append((begin,len(prices),h+w))
    # Dual: maximize sum group minima of seam prices + signed score
    # price, minus the required score. Each seam price and the score
    # price are bounded for numerical stability only.
    # Implement the primal with exact normalization, soft other equations.
    n=len(index);m=len(groups);A=hp.Highs()
    A.setOptionValue('output_flag',False);A.setOptionValue('threads',1)
    rhs=np.zeros(m+n+1);A.addRows(len(rhs),rhs,rhs,0,[0]*(len(rhs)+1),[],[])
    starts=array('i',[0]);inds=array('i');vals=array('d')
    for j,(s,e,_) in enumerate(groups):
        for t in range(s,e):
            v={j:1}
            for b in signed[4*t:4*t+4]:
                if b:
                    z=m+abs(b)-1;v[z]=v.get(z,0)+(1 if b>0 else -1)
            if prices[t]:v[m+n]=prices[t]
            for b,c in v.items():
                if c:inds.append(b);vals.append(c)
            starts.append(len(inds))
    if not hard:
        for j in range(m,len(rhs)):
            for c in (1,-1):
                inds.append(j);vals.append(c);starts.append(len(inds))
    size=len(starts)-1;obj=np.ones(size);obj[:len(prices)]=0
    A.addCols(size,obj,np.zeros(size),np.full(size,hp.kHighsInf),len(inds),starts,inds,vals)
    return A,groups,prices,signed,n

def test(axis,k=39,q=1,gx=28,gy=8,train=(13,),hard=False):
    import numpy as np
    import highspy as hp
    A,gs,c,s,n=setup(axis,k,q,gx,gy,hard);m=len(gs)
    print('axis',axis,'quadruple variables',len(c),'seam equations',n,flush=True)
    for t in train:
        L=14*t;D=5*k-1+(k-5)//7+72*t
        rhs=np.array([float(L**degree) for _,_,degree in gs])
        A.changeRowsBounds(m,np.arange(m,dtype=np.int32),rhs,rhs)
        A.changeRowBounds(m+n,D,D)
        A.run();stat=A.getModelStatus()
        if stat==hp.HighsModelStatus.kInfeasible:
            status,has,ray=A.getDualRay()
            print('hard infeasible, ray?',has,flush=True)
            if not has:continue
        else:
            assert stat==hp.HighsModelStatus.kOptimal
            ray=A.getSolution().row_dual
        Z=10000;du=[round(p*Z) for p in ray];ps=[0,*du[m:m+n]];last=du[m+n]
        # For an exact board the total seam flow is zero. Price of any
        # chosen quadruple plus the signed price of its marks is at
        # least the minimum on its own normalization row.
        coef=[0]*3
        for a,b,deg in gs:
            low=min(-last*c[i]-sum(ps[abs(z)]*(1 if z>0 else -1) for z in s[4*i:4*i+4])
                    for i in range(a,b))
            coef[deg]+=low*14**deg
        coef[0]+=last*(5*k-1+(k-5)//7);coef[1]+=last*72
        print('train',t,'soft residual',A.getObjectiveValue(),'integer separator',coef,
              'value',sum(v*t**j for j,v in enumerate(coef)),flush=True)
if __name__=='__main__':
    import sys
    test(int(sys.argv[1]),train=tuple(map(int,sys.argv[2:] or [13])))
