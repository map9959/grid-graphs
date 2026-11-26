"""Couple a full-width forest strip to the diagonal sector chart."""
from .seven_threshold import move,masks,Counter,defaultdict,MASKS,SYM,trans
from .patch_square import relaxation
from functools import lru_cache
from itertools import product

def run(n,H,d,w):
    import highspy as hs
    import numpy as np
    base=43+(n-43)%6;S=n-2
    assert H-2<=d+3
    ns,rows,obj=relaxation(base,d+4,pooled=d,period=3,diagonal=w)
    def pos(i,j,side,h):
        axis=lambda a:a if a<h else 2*h+3+a-side if a>=side-h else h+(a-h)%3
        clip=lambda a:max(-w-5,min(w+5,a))
        return axis(i),axis(j),clip(i-j),clip(i+j+1-side)
    def position(r,j):return tuple(pos(a,b,S,d+3) for g in range(8) for a,b in [trans(r,j,S,g)])
    counts=[Counter(pos(i,j,s,h) for i,j in product(range(s),repeat=2)) for s,h in ((n,d+4),(S,d+3))]
    inv={x:k for k,x in ns.items()};xs=list(inv);ix={x:i for i,x in enumerate(xs)}
    lp=hs.Highs();lp.setOptionValue('threads',1);lp.setOptionValue('output_flag',False)
    import sys
    if '--exact' not in sys.argv:lp.setOptionValue('solver','ipm');lp.setOptionValue('run_crossover','off')
    lp.addVars(len(xs),np.zeros(len(xs)),np.full(len(xs),hs.kHighsInf));lp.setMaximize()
    lp.changeColsCost(len(xs),np.arange(len(xs)),[obj.get(x,0) for x in xs])
    for cs,op,b in rows:
        if op=='=' and b:
            tag,atom=inv[cs[0][0]];b=counts[int(tag=='p')][atom[0]]
        lp.addRow(b if op!='<=' else -hs.kHighsInf,b if op!='>=' else hs.kHighsInf,len(cs),[ix[x] for x,v in cs],[v for x,v in cs])
    rid={};lut=np.zeros((S,H-2,512),dtype=np.int32)
    for j,r in product(range(S),range(H-2)):
        p=position(r,j)
        for m in MASKS:
            key=(r,p[0],m)
            if key not in rid:
                x=ns['p',min(zip(p,SYM[m]))];rid[key]=lp.getNumRow();lp.addRow(0,0,1,[ix[x]],[-1])
            lut[j,r,m]=rid[key]
    @lru_cache(None)
    def transitions(st):
        arcs=[];dest=set()
        for i,(a,b,p) in enumerate(st):
            for c in range(1<<H):
                q=move(b,p,c)
                if q is None:continue
                z=b,c,q;arcs.append((i,z,masks(a,b,c,H)));dest.add(z)
        nxt=tuple(sorted(dest));idx={q:i for i,q in enumerate(nxt)}
        return nxt,np.array([i for i,z,ms in arcs]),np.array([idx[z] for i,z,ms in arcs]),np.array([ms for i,z,ms in arcs])
    st=((0,0,tuple(range(H))),);src=lp.getNumRow();lp.addRow(1,1,0,[],[])
    for j in range(n):
        nxt,fr,to,ms=transitions(st);end=lp.getNumRow();E=len(fr);K=1+(j<n-1)+(H-2 if j>=2 else 0)
        if j<n-1:lp.addRows(len(nxt),np.zeros(len(nxt)),np.zeros(len(nxt)),0,[],[],[])
        ids=np.empty((E,K),dtype=np.int32);cost=np.ones((E,K));ids[:,0]=src+fr
        if j<n-1:ids[:,1]=end+to;cost[:,1]=-1
        if j>=2:ids[:,-(H-2):]=lut[j-2,np.arange(H-2),ms]
        lp.addCols(E,np.zeros(E),np.zeros(E),np.full(E,hs.kHighsInf),E*K,np.arange(0,E*K,K,dtype=np.int32),ids.ravel(),cost.ravel());st=nxt;src=end
    print('side',n,'height',H,'columns',lp.getNumCol(),'rows',lp.getNumRow(),flush=True)
    lp.run();assert lp.getModelStatus()==hs.HighsModelStatus.kOptimal
    print('diagonal-strip numerical upper',lp.getObjectiveValue(),flush=True)
    from pathlib import Path
    import json
    sol=lp.getSolution().row_dual
    Path(f'target/diagonal_strip{H}_{n}.json').write_text(json.dumps([sol[:len(rows)],[[k,sol[i]] for k,i in rid.items() if sol[i]]],separators=(',',':')))
if __name__=='__main__':
    import sys
    run(*map(int,sys.argv[1:5]))
