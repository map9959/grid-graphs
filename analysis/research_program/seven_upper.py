"""Integer replay of a seven-row dual: price every full-width forest path."""
from .seven_threshold import *
from .six_joint_replay import projected

def price(cost,scale):
    import numpy as np
    # Bound every partial sum below the int64 sentinel.
    assert 545*max(map(abs,cost.values()),default=0)<2**60
    @lru_cache(None)
    def block(st):
        arcs=[];ds=set()
        for i,(a,b,p) in enumerate(st):
            for c in range(128):
                q=move(b,p,c)
                if q is None:continue
                d=(b,c,q);ds.add(d);arcs.append((i,d,masks(a,b,c)))
        nxt=tuple(sorted(ds));idx={v:i for i,v in enumerate(nxt)}
        return nxt,np.array([s for s,_,_ in arcs]),np.array([idx[d] for _,d,_ in arcs]),np.array([m for _,_,m in arcs])
    @lru_cache(None)
    def weights(st,h):
        if h<0:return 0
        lut=np.zeros((5,512),dtype=np.int64)
        for r in range(5):
            for m in MASKS:lut[r,m]=cost.get((h,r,m),0)
        return lut[np.arange(5),block(st)[3]].sum(axis=1)
    st=(start,);v=np.zeros(1,dtype=np.int64);count=0
    for j in range(109):
        nxt,s,d,_=block(st);w=weights(st,axis(j-2,107) if j>=2 else -1)
        z=np.full(len(nxt),2**61,dtype=np.int64);np.minimum.at(z,d,v[s]+w)
        assert max(z)<2**60
        st=nxt;v=z;count+=len(s)
    return Q(int(min(v)),scale),count

def check(build=False,source='target/seven_sparse_candidate.json'):
    ns,A,b,obj,labels=model();scale=10**8
    path=file.with_name('seven_upper_109.json')
    if build:
        raw,cs=json.loads(Path(source).read_text())
        assert len(raw)==len(A) and len(cs)==len(labels)
        y={i:Q(round(q*scale),scale) for i,q in enumerate(raw) if q}
        cost={k:round(q*scale) for k,q in zip(labels,cs) if q}
        rc=projected(A,b,obj,labels,y,{k:Q(q,scale) for k,q in cost.items()})
        normal={}
        for i,((row,op),bb) in enumerate(zip(A,b)):
            if bb>0 and op=='=' and all(w>0 for x,w in row):
                for x,w in row:normal[x]=(i,w)
        adj=Counter()
        for x,z in rc.items():
            if z>0:
                i,w=normal[x];adj[i]=max(adj[i],z/w)
        for i,q in adj.items():y[i]=y.get(i,0)+q
    else:
        yy,cc=json.loads(path.read_text());y={int(i):Q(q) for i,q in yy.items()};cost={tuple(k):q for k,q in cc}
    assert max(projected(A,b,obj,labels,y,{k:Q(q,scale) for k,q in cost.items()}).values())<=0
    best,n=price(cost,scale);ub=sum(w*b[i] for i,w in y.items())-best
    print('exact seven-row upper',ub,'=',float(ub),'legal arcs',n,flush=True)
    if build and ub<Q(12293,3):
        path.write_text(json.dumps([{i:str(q) for i,q in y.items() if q},[[k,q] for k,q in cost.items() if q]],separators=(',',':'))+'\n')
    return ub

if __name__=='__main__':
    import sys
    check('--build' in sys.argv)
