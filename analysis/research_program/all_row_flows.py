"""Simultaneous full-width forest flows for every H-row band on a sector chart."""
from .diagonal_ribbon import setup
from .seven_threshold import move,masks,Counter,defaultdict,SYM,MASKS,trans
from itertools import product
from functools import lru_cache
import sys

def run(n,H,d,w):
    import highspy as hs
    import numpy as np
    ns,ix,lp,row,coef,pos=setup(n,H,d,w);S=n-2;D=min(2,d+5-H);assert D>=0
    def chart(N,detail):
        def ax(z,T):return z if z<D else 2*D+3+z-T if z>=T-D else D+(z-D)%3
        def typ(i,j):
            if j==N:return None
            cut=lambda z:max(-w,min(w,z))
            return ax(i,N+1-H),ax(j,N),cut(i-j),cut(i+j+1-N)
        cnt=Counter();starts=Counter();patch=defaultdict(dict)
        for i in range(N+1-H):
            starts[typ(i,0)]+=1
            for j in range(N):
                a,b=typ(i,j),typ(i,j+1);cnt[a,b]+=1
                if not detail or j<2:continue
                for r in range(H-2):
                    z=tuple(pos(u,v,N-2,d+3) for g in range(8) for u,v in [trans(i+r,j-2,N-2,g)])
                    patch[a,r][z[0]]=z
        return cnt,starts,patch
    cnt,starts,patch=chart(n,True);dc,ds,_=chart(n+6,False);ec,es,_=chart(n+12,False)
    assert cnt.keys()==dc.keys()==ec.keys() and starts.keys()==ds.keys()==es.keys()
    # At fixed offset each fine patch bucket contributes to a unique
    # coarse band-stage marginal. Positions without a covering band
    # at this offset form separate fine types.
    for r in range(H-2):
        allkeys=set()
        for (k,rr),p in patch.items():
            if r==rr:assert not allkeys.intersection(p);allkeys.update(p)
    labels={}
    for (a,r),zs in patch.items():
        for m in MASKS:
            c=Counter(ix[ns['p',min(zip(z,SYM[m]))]] for z in zs.values());labels[a,r,m]=row(0,0,[(j,-v) for j,v in c.items()])
    @lru_cache(None)
    def arcs(s):
        a,b,p=s;out=[]
        for c in range(1<<H):
            P=move(b,p,c)
            if P is not None:out.append(((b,c,P),masks(a,b,c,H)))
        return out
    start=(0,0,tuple(range(H)));states={start};layers=[];index=[]
    for j in range(n):
        if not layers or states!=layers[-1]:layers.append(states)
        index.append(len(layers)-1);states={v for s in states for v,_ in arcs(s)}
        if states==layers[-1]:
            index.extend([len(layers)-1]*(n-j-1));break
    @lru_cache(None)
    def flow(a,s):return row(0,0)
    rhs=[]
    for a,b in starts.items():
        j=flow(a,start);lp.changeRowBounds(j,b,b);rhs.append((j,b,ds[a]-b,es[a]-2*ds[a]+b))
    # If width pooling identifies early and steady states, allowing all
    # reachable states is a relaxation. Only the start has a source.
    for (a,b),amt in cnt.items():
        j=0 if a[1]==0 else 1 if a[1]==1 else n-1
        pool=layers[index[j]] if D>=2 else layers[-1]
        nr=row(amt,amt);rhs.append((nr,amt,dc[a,b]-amt,ec[a,b]-2*dc[a,b]+amt))
        ids=[];v=[];off=[]
        for s in sorted(pool):
            fr=flow(a,s)
            for u,ms in arcs(s):
                off.append(len(ids));ids.extend([nr,fr]);v.extend([1.,1.])
                if b is not None:ids.append(flow(b,u));v.append(-1.)
                if (a,0) in patch:
                    ids.extend(labels[a,r,m] for r,m in enumerate(ms));v.extend([1.]*(H-2))
        K=len(off);lp.addCols(K,np.zeros(K),np.zeros(K),np.full(K,hs.kHighsInf),len(ids),np.array(off,dtype=np.int32),np.array(ids,dtype=np.int32),np.array(v))
    print('all-row model',n,H,'columns',lp.getNumCol(),'rows',lp.getNumRow(),flush=True)
    lp.run();print('result',lp.getModelStatus(),lp.getObjectiveValue(),flush=True)
    if lp.getModelStatus()==hs.HighsModelStatus.kOptimal:
        y=lp.getSolution().row_dual
        poly=[sum(v[j]*z for v,z in zip(coef,y))+sum(y[i]*c[j] for i,*c in rhs) for j in range(3)]
        print('candidate Newton coefficients',poly,flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
