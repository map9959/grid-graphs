"""A joint forest on the moving ribbon of sites (row-column) in a fixed interval."""
from .diagonal_strip import relaxation,SYM,trans,Counter,defaultdict,product,lru_cache
from .seven_threshold import spread
from .chart_counts import count
import sys

@lru_cache(None)
def step(b,p,c,valid,first):
    H=len(p);ds=list(p)+list(range(H,2*H))
    def rt(a):
        while ds[a]!=a:a=ds[a]
        return a
    def edge(a,b):
        a,b=rt(a),rt(b);ds[a]=b;return a!=b
    for r in range(H):
        if r+1<H and not first and ((b>>(r+1)|c>>r)&1) and not edge(r+1,H+r):return
        if r+1<H and valid>>r&3==3 and c>>r&3 and not edge(H+r,H+r+1):return
    v=[rt(H+r) for r in range(H)];return tuple(v.index(x) for x in v)

def setup(n,H,d,w):
    import highspy as hs
    import numpy as np
    base=43+(n-43)%6;S=n-2
    ns,rr,obj=relaxation(base,d+4,pooled=d,period=3,diagonal=w)
    def pos(i,j,S,h):
        ax=lambda a:a if a<h else 2*h+3+a-S if a>=S-h else h+(a-h)%3
        clip=lambda a:max(-w-5,min(w+5,a))
        return ax(i),ax(j),clip(i-j),clip(i+j+1-S)
    xs=list(ns.values());ix={x:i for i,x in enumerate(xs)};inv={x:k for k,x in ns.items()}
    lp=hs.Highs();lp.setOptionValue('threads',1);lp.setOptionValue('output_flag',False)
    lp.setOptionValue('solver','ipm');lp.setOptionValue('run_crossover','off')
    lp.addVars(len(xs),np.zeros(len(xs)),np.full(len(xs),hs.kHighsInf));lp.setMaximize()
    lp.changeColsCost(len(xs),np.arange(len(xs)),[obj.get(x,0) for x in xs]);I=hs.kHighsInf
    def row(a,b,cs=()):
        k=lp.getNumRow();lp.addRow(float(a),float(b),len(cs),[j for j,z in cs],[float(z) for j,z in cs]);return k
    coeff=[]
    for cs,op,b in rr:
        abc=(b,0,0)
        if op=='=' and b>0:
            tag,atom=inv[cs[0][0]];q=int(tag=='p');abc=count(n-2*q,d+4-q,w+5,atom[0])
        coeff.append(abc);b=abc[0];row(b if op!='<=' else -I,b if op!='>=' else I,[(ix[x],z) for x,z in cs])
    return ns,ix,lp,row,coeff,pos

def run(n,H,d,w):
    import numpy as np
    import highspy as hs
    ns,ix,lp,row,coeff,pos=setup(n,H,d,w);S=n-2;I=hs.kHighsInf
    center=H//2;labels={};norm=[];D=d+w+H+6
    def phase(j,N):
        edge=j if j<D else 2*D+3+j-N if j>=N-D else D+(j-D)%3
        return edge,max(-D,min(D,2*j+1-N))
    stages=Counter((phase(j,n),phase(j+1,n) if j+1<n else None) for j in range(n))
    future=Counter((phase(j,n+6),phase(j+1,n+6) if j+1<n+6 else None) for j in range(n+6))
    assert stages.keys()==future.keys()
    def edgekey(j):
        return (phase(j,n),phase(j+1,n) if j+1<n else None)
    pkeys={}
    for j in range(2,n):
        for r in range(H-4):
            i=j-center+r
            if 0<=i<S:
                z=tuple(pos(a,b,S,d+3) for g in range(8) for a,b in [trans(i,j-2,S,g)])
                assert abs(i-j+2)<w+5
                pkeys[j,r]=z
    @lru_cache(None)
    def label(z,m):
        k=(z[0],m)
        if k not in labels:labels[k]=row(0,0,[(ix[ns['p',min(zip(z,SYM[m]))]],-1)])
        return labels[k]
    @lru_cache(None)
    def flow(h,s):return row(0,0)
    @lru_cache(None)
    def arcs(s,valid,first):
        a,b,p=s;out=[]
        for c in range(1<<H):
            if c&~valid:continue
            q=step(b,p,c,valid,first)
            if q is None:continue
            ms=tuple(spread(a>>(r+2))+2*spread(b>>(r+1))+4*spread(c>>r) for r in range(H-4))
            out.append(((b,c,q),ms))
        return out
    start=0,0,tuple(range(H));states={start};groups=defaultdict(set);represent={}
    for j in range(n):
        valid=sum(1<<r for r in range(H) if 0<=j-center+r<n);k=edgekey(j);info=(valid,tuple(pkeys.get((j,r)) for r in range(H-4)))
        assert represent.setdefault(k,info)==info
        groups[k].update(states);states={z for s in states for z,_ in arcs(s,valid,j==0)}
    first=phase(0,n);initial=flow(first,start);lp.changeRowBounds(initial,1,1)
    for (h,g),ss in sorted(groups.items(),key=lambda v:str(v[0])):
        valid,zs=represent[h,g];amt=stages[h,g];nr=row(amt,amt);norm.append((nr,amt,future[h,g]-amt))
        indices=[];vals=[];off=[]
        for s in sorted(ss):
            fr=flow(h,s)
            for dest,ms in arcs(s,valid,h==first):
                off.append(len(indices));indices.extend((nr,fr));vals.extend((1,1))
                if g is not None:indices.append(flow(g,dest));vals.append(-1)
                for z,m in zip(zs,ms):
                    if z:indices.append(label(z,m));vals.append(1)
        E=len(off);lp.addCols(E,np.zeros(E),np.zeros(E),np.full(E,I),len(indices),np.array(off,dtype=np.int32),np.array(indices,dtype=np.int32),np.array(vals,dtype=float))
    print('ribbon',H,n,'model',lp.getNumCol(),lp.getNumRow(),flush=True)
    lp.run();print('status',lp.getModelStatus(),'candidate',lp.getObjectiveValue(),flush=True)
    if lp.getModelStatus()==hs.HighsModelStatus.kOptimal:
        y=lp.getSolution().row_dual
        poly=[sum(v[j]*z for v,z in zip(coeff,y)) for j in range(3)];poly[0]+=y[initial]
        for i,b0,b1 in norm:poly[0]+=y[i]*b0;poly[1]+=y[i]*b1
        print('ribbon numerical Newton',poly,flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
