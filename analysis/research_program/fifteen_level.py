"""Project prices onto the core/word inequalities needed to exclude 4092."""
from .fourteen_bound import *

def run():
    import numpy as np
    import highspy as hs
    ns,A,b,obj,l,*_=core15();offsets=(0,6);labs=layout(l,[(o,9) for o in offsets])
    keys=list(labs);xs=list(ns.values());ix={x:i for i,x in enumerate(xs)}
    ci=np.array([ix[labs[k]] for k in keys]);ki={k:i for i,k in enumerate(keys)}
    mirror={fine_axis(j,15):fine_axis(106-j,15) for j in range(107)}
    refl=[ki[o,mirror[h],r,((m&73)<<2)|(m&146)|((m&292)>>2)] for o,h,r,m in keys]
    # Typical mass in a bulk type is 30 times that of a pinned type.
    count=Counter(fine_axis(j,15) for j in range(107));metric=np.array([1/count[k[1]] for k in keys])
    pp=json.loads(pathspec(15)[1].read_text())[0];x0=np.array([float(Q(pp.get(labs[k],0))) for k in keys])
    h=hs.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False);h.setOptionValue('solver','ipm');h.setOptionValue('run_crossover','off')
    h.addVars(len(xs),np.zeros(len(xs)),np.full(len(xs),hs.kHighsInf));h.setMaximize()
    norms={};aggs=[];base=np.array([obj.get(x,0) for x in xs])
    for i,((cs,op),bb) in enumerate(zip(A,b)):
        h.addRow(float(bb) if op!='<=' else -hs.kHighsInf,float(bb) if op!='>=' else hs.kHighsInf,len(cs),[ix[x] for x,w in cs],[float(w) for x,w in cs])
        if bb>0 and op=='=' and all(w>0 for x,w in cs):
            for x,w in cs:norms[x]=i,w
        if bb==0 and any(x[0] in 'fghij' and w>0 for x,w in cs) and len({x[0] for x,w in cs})>1:aggs.append((i,cs))
    raw=json.loads(Path('target/fifteen_balanced.json').read_text())
    c0={tuple(k):q/scale for k,q in raw[1]};center=np.array([c0.get(k,0) for k in keys])
    v0=sum(float(Q(q))*b[int(i)] for i,q in raw[0].items())-np.dot(x0,center)-4091.98
    normals=[];rhs=[];seen=set();dual=np.empty(0);best=None
    def cut(u,sign,limit):
        zz=(u+u[refl])/2
        vec=np.append(metric*zz,sign)
        norm=np.linalg.norm(vec);assert norm>0
        fingerprint=hash((vec.round(5).tobytes(),round(limit,5)))
        if fingerprint not in seen:
            seen.add(fingerprint);normals.append(vec/norm);rhs.append((np.dot(u,center)+sign*v0-limit)/norm)
    for it in range(150):
        adj=np.zeros(len(keys))
        if normals:
            M=np.stack(normals);G=M@M.T
            dual=np.pad(dual,(0,len(M)-len(dual)));res=np.array(rhs)-G@dual
            for _ in range(3000):
                i=np.argmax(np.where(dual>0,abs(res),res));q=max(-dual[i],res[i]/G[i,i])
                dual[i]+=q;res-=q*G[:,i]
                if abs(q)<1e-8:break
            adj=-(dual@M)[:-1]*metric
        cost_int=np.floor((center+adj)*scale).astype('int64')
        costs={k:int(q) for k,q in zip(keys,cost_int) if q}
        h.changeColsCost(len(xs),np.arange(len(xs)),base+np.bincount(ci,weights=cost_int/scale,minlength=len(xs)))
        h.run();assert h.getModelStatus()==hs.HighsModelStatus.kOptimal
        sol=h.getSolution();p=np.array(sol.col_value)
        cut(p[ci]-x0,-1,4091.97-np.dot(base,p))
        y={i:Q(round(q*scale),scale) for i,q in enumerate(sol.row_dual) if q}
        rc=projected(A,b,obj,labs,y,{k:Q(q,scale) for k,q in costs.items()})
        for i,cs in reversed(aggs):
            q=max([rc[x]/w for x,w in cs if w>0 and x not in norms]+[0])
            if q>0:
                y[i]=y.get(i,0)+q
                for x,w in cs:rc[x]-=w*q
        inc=Counter()
        for x,z in rc.items():
            if z>0:
                i,w=norms[x];inc[i]=max(inc[i],z/w)
        for i,q in inc.items():y[i]=y.get(i,0)+q
        assert max(projected(A,b,obj,labs,y,{k:Q(q,scale) for k,q in costs.items()}).values())<=0
        core=sum(q*b[i] for i,q in y.items());budget=((core-4092)*scale).__floor__()
        d,n,aa=oracle(costs,budget,'paths',15);ub=core-d
        print(it,'rows',len(rhs),'upper',float(ub),flush=True)
        if best is None or ub<best:
            best=ub;data=json.dumps([{i:str(q) for i,q in y.items() if q},[[k,q] for k,q in costs.items() if q],budget],separators=(',',':'))+'\n'
            Path('target/fifteen_level.json').write_text(data)
            if best<4092:file.with_name('fifteen_upper_109.json').write_text(data);assert check(15)<4092;return
        if not aa:_,_,aa=oracle(costs,budget,'beam',15)
        layers=defaultdict(list)
        for j,s,c in aa:layers[j].append((s,c))
        dp={pathspec(15)[0]:0};hist=[]
        for j in range(109):
            pr={};nd={};phase=fine_axis(j-2,15)
            for s,c in layers[j]:
                if s not in dp:continue
                a,v,p=s;dst=v,c,move(v,p,c);z=dp[s]
                if j>=2:
                    ms=masks(a,v,c,15);z+=sum(costs.get((o,phase,r,m),0) for o in offsets for r,m in enumerate(ms[o:o+7]))
                if dst not in nd or z<nd[dst]:nd[dst]=z;pr[dst]=s,c
            dp=nd;hist.append(pr)
        for dst in sorted(dp,key=dp.get)[:16]:
            ct=np.zeros(len(keys))
            for j in reversed(range(109)):
                dst,c=hist[j][dst]
                if j>=2:
                    ms=masks(*dst[:2],c,15)
                    for o in offsets:
                        for r,m in enumerate(ms[o:o+7]):ct[ki[o,fine_axis(j-2,15),r,m]]+=1
            cut(x0-ct,1,0)

if __name__=='__main__':run()
