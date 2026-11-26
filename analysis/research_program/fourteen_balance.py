"""Price redistribution between symmetry-equivalent events, using a word-cut QP."""
from .fourteen_bound import *

def run(height=14):
    import numpy as np
    stem='fifteen' if height==15 else 'fourteen';target=4107-height
    ns,A,b,obj,l,*_=(core15 if height==15 else core14)();blocks=[(0,9),(height-9,9)]
    labs=layout(l,blocks);keys=list(labs);idx={k:i for i,k in enumerate(keys)}
    ids={x:i for i,x in enumerate(sorted(set(labs.values())))};groups=np.array([ids[labs[k]] for k in keys])
    counts=np.bincount(groups);mirror={fine_axis(j,height):fine_axis(106-j,height) for j in range(107)}
    refl=np.array([idx[o,mirror[h],r,((m&73)<<2)|(m&146)|((m&292)>>2)] for o,h,r,m in keys])
    assert np.all(groups[refl]==groups)
    # In the metric below all events sharing an orbit have equal scale.
    totals=Counter(fine_axis(j,height) for j in range(107));weight=np.array([1/totals[k[1]] for k in keys])
    # Orthogonal projection onto the subspace summing to zero per variable.
    def proj(v):
        v=(v+v[refl])/2
        return v-np.bincount(groups,weights=v)[groups]/counts[groups]
    weights=np.zeros(len(keys));ref=None;best=None;words=[];seen=set();coef=np.array([])
    for it in range(120):
        if ref is None or it%8==0:
            p=Path(f'target/{stem}_'+('main' if height==15 else 'restart')+'.json');yp,cc,_=json.loads(p.read_text())[:3]
            y={int(i):Q(q) for i,q in yp.items()};ref={tuple(k):q for k,q in cc}
            rhs=sum(q*b[i] for i,q in y.items());cv=np.array([ref.get(k,0)/scale for k in keys])
            assert max(projected(A,b,obj,labs,y,{k:Q(v,scale) for k,v in ref.items()}).values())<=0
        # Minimize squared adjustment subject to all observed path inequalities.
        # Coordinate ascent on nonnegative dual coefficients for the projection QP.
        if words:
            V=np.stack([proj(w)*weight for w in words]);G=V@V.T
            h=np.array([float(rhs)-(target-.06)-np.dot(cv,w) for w in words])
            coef=np.pad(coef,(0,len(words)-len(coef)));z=h-G@coef
            for rnd in range(2000):
                ix=int(np.argmax(np.where(coef>0,abs(z),z)/np.sqrt(G.diagonal()+1e-8)))
                inc=max(-coef[ix],z[ix]/(G[ix,ix]+1e-9));coef[ix]+=inc;z-=inc*G[:,ix]
                if abs(inc)<1e-10 or coef[ix]>1000:break
            weights=proj(weight*(coef@V))
        cost={k:ref.get(k,0)+int(np.floor(w*scale)) for k,w in zip(keys,weights)}
        # Remove rounding errors per orbit before accepting a candidate.
        rc=projected(A,b,obj,labs,y,{k:Q(v,scale) for k,v in cost.items()})
        for k,x in labs.items():
            if rc.get(x,0)>0:
                z=-((-rc[x]*scale).__floor__());cost[k]-=z;rc[x]-=Q(z,scale)
        assert max(rc.values())<=0
        budget=((rhs-target)*scale).__floor__();d,n,aa=oracle(cost,budget,'paths',height);ub=rhs-d
        print(it,'words',len(words),'exact upper',float(ub),flush=True)
        if best is None or ub<best:
            best=ub;data=json.dumps([{i:str(q) for i,q in y.items() if q},[[k,q] for k,q in cost.items() if q],budget],separators=(',',':'))+'\n'
            Path(f'target/{stem}_balanced.json').write_text(data)
            if ub<target:file.with_name(stem+'_upper_109.json').write_text(data);assert check(height)<target;return
        if not aa:_,_,aa=oracle(cost,budget,'beam',height)
        layers=defaultdict(list)
        for j,s,c in aa:layers[j].append((s,c))
        dp={pathspec(height)[0]:0};hist=[]
        for j in range(109):
            nd={};pred={};h=fine_axis(j-2,height)
            for s,c in layers[j]:
                if s not in dp:continue
                a,v,p=s;dst=v,c,move(v,p,c);z=dp[s]
                if j>=2:
                    ms=masks(a,v,c,height);z+=sum(cost[o,h,r,m] for o,H in blocks for r,m in enumerate(ms[o:o+7]))
                if dst not in nd or z<nd[dst]:nd[dst]=z;pred[dst]=s,c
            dp=nd;hist.append(pred)
        for dest in sorted(dp,key=dp.get)[:12]:
            w=[];dst=dest
            for pr in reversed(hist):dst,c=pr[dst];w.append(c)
            w=tuple(reversed(w))
            if w not in seen:
                seen.add(w);v=np.zeros(len(keys))
                for j in range(107):
                    ms=masks(*w[j:j+3],height)
                    for o,H in blocks:
                        for r,m in enumerate(ms[o:o+7]):v[idx[o,fine_axis(j,height),r,m]]+=1
                words.append(v)

if __name__=='__main__':
    import sys
    run(15 if '--fifteen' in sys.argv else 14)
