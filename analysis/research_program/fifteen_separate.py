"""Separate the 4092 core slice from the joint strip's word distribution."""
from .fourteen_bound import *

def run():
    import numpy as np
    from scipy import sparse
    import osqp,highspy as hs
    ns,A,b,obj,l,*_=core15();bl=[(0,9),(6,9)];labs=layout(l,bl);keys=list(labs)
    idx={k:i for i,k in enumerate(keys)};xs=list(ns.values());xi={x:i for i,x in enumerate(xs)};ci=np.array([xi[labs[k]] for k in keys])
    mir={fine_axis(j,15):fine_axis(106-j,15) for j in range(107)}
    rf=[idx[o,mir[h],r,((m&73)<<2)|(m&146)|((m&292)>>2)] for o,h,r,m in keys]
    cnt=Counter(fine_axis(j,15) for j in range(107));metric=np.array([1/cnt[h] for o,h,r,m in keys])
    pp=json.loads(pathspec(15)[1].read_text())[0];x0=np.array([float(Q(pp.get(x,0))) for x in labs.values()])
    h=hs.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False);h.setOptionValue('solver','ipm');h.setOptionValue('run_crossover','off')
    h.addVars(len(xs),np.zeros(len(xs)),np.full(len(xs),hs.kHighsInf));h.setMaximize()
    norms={};agg=[]
    for i,((cs,op),bb) in enumerate(zip(A,b)):
        h.addRow(float(bb) if op!='<=' else -hs.kHighsInf,float(bb) if op!='>=' else hs.kHighsInf,len(cs),[xi[x] for x,w in cs],[float(w) for x,w in cs])
        if bb>0 and op=='=' and all(w>0 for x,w in cs):
            for x,w in cs:norms[x]=i,w
        if bb==0 and any(x[0] in 'fghij' and w>0 for x,w in cs) and len({x[0] for x,w in cs})>1:agg.append((i,cs))
    h.addRow(4092,4092,len(obj),[xi[x] for x in obj],list(obj.values()))
    _,cc,_,*_=json.loads(Path('target/fifteen_aspire.json').read_text());ref={tuple(k):v/scale for k,v in cc}
    center=np.array([ref.get(k,0) for k in keys]);ct0=np.dot(x0,center)
    vectors=[];rhs=[];seen=set();best=None;G=np.empty((0,0))
    def add(v,sgn):
        # q=sgn*(event-x0), with +1 for a core and -1 for a word.
        q=.5*(v+v[rf])-x0;sig=(sgn,hash(q.round(5).tobytes()))
        if sig in seen:return
        seen.add(sig);z=sgn*q
        # Affine intercept t = ct0 + bias; translation cancels between sides.
        vec=np.append(z*metric,-sgn);norm=np.linalg.norm(vec)
        vectors.append(vec/norm);rhs.append((-.025-np.dot(z,center))/norm)
    def addword(w):
        ct=np.zeros(len(keys))
        for j in range(107):
            ms=masks(*w[j:j+3],15)
            for o,_ in bl:
                for r,m in enumerate(ms[o:o+7]):ct[idx[o,fine_axis(j,15),r,m]]+=1
        add(ct,-1)
    def extract(arcs,cost):
        import random
        rng=random.Random(len(vectors)+15);g=defaultdict(list)
        for j,s,c in arcs:g[j].append((s,c))
        hist=[];val={}
        for j in reversed(range(109)):
            opts=defaultdict(list);phase=fine_axis(j-2,15)
            for s,c in g[j]:
                a,v,p=s;d=v,c,move(v,p,c)
                if j!=108 and d not in val:continue
                z=val.get(d,0);ms=masks(a,v,c,15)
                if j>=2:z+=sum(cost.get((o,phase,r,m),0) for o,_ in bl for r,m in enumerate(ms[o:o+7]))
                opts[s].append((z,c,d))
            for op in opts.values():op.sort()
            val={s:v[0][0] for s,v in opts.items()};hist.append(opts)
        for i in range(80):
            s=pathspec(15)[0];w=[]
            for layer in reversed(hist):
                op=layer[s];lim=op[0][0]+int(.01*(i%8)*scale)
                _,c,s=rng.choice([v for v in op if v[0]<=lim]);w.append(c)
            addword(w)
    for it in range(120):
        adj=np.zeros(len(keys))
        if vectors:
            M=np.stack(vectors);k=len(G);m=len(M)
            if m>k:
                z=M[k:]@M.T;old=G;G=np.empty((m,m));G[:k,:k]=old;G[k:,:]=z;G[:,k:]=z.T
            v,U=np.linalg.eigh(G);ok=v>1e-9;L=U[:,ok]*np.sqrt(v[ok]);n=L.shape[1]
            qp=osqp.OSQP();qp.setup(P=sparse.eye(n,format='csc'),q=np.zeros(n),A=sparse.csc_matrix(L),l=np.full(m,-np.inf),u=np.array(rhs),verbose=False,eps_abs=1e-7,eps_rel=1e-7,max_iter=100000)
            sol=qp.solve();assert sol.info.status_val in (1,2),sol.info.status
            adj=(((U[:,ok]@(sol.x/np.sqrt(v[ok])))@M)[:-1])*metric
        cv=np.rint((center+adj)*scale).astype('int64');cost={k:int(q) for k,q in zip(keys,cv) if q}
        h.changeColsCost(len(xs),np.arange(len(xs)),np.bincount(ci,weights=cv/scale,minlength=len(xs)))
        h.run();assert h.getModelStatus()==hs.HighsModelStatus.kOptimal;sol=h.getSolution()
        yy=sol.row_dual;mu=Q(round(yy[-1]*scale),scale)
        y={i:Q(round(q*scale),scale) for i,q in enumerate(yy[:-1]) if q}
        rc=projected(A,b,{x:-mu*v for x,v in obj.items()},labs,y,{k:Q(q,scale) for k,q in cost.items()})
        for i,cs in reversed(agg):
            z=max([rc[x]/w for x,w in cs if w>0 and x not in norms]+[0])
            if z>0:
                y[i]=y.get(i,0)+z
                for x,w in cs:rc[x]-=w*z
        inc=Counter()
        for x,z in rc.items():
            if z>0:
                i,w=norms[x];inc[i]=max(inc[i],z/w)
        for i,q in inc.items():y[i]=y.get(i,0)+q
        bound=sum(q*b[i] for i,q in y.items());budget=((bound+4092*mu)*scale).__floor__()
        d,_,aa=oracle(cost,budget,'paths',15)
        print(it,'constraints',len(vectors),'slice gap',float(bound+4092*mu-d),'score multiplier',float(mu),flush=True)
        if mu<0:
            # Express this separating dual in the same unit-objective
            # convention as the standalone checker, rounding prices down.
            Y={i:q/(-mu) for i,q in y.items()};C={k:(Q(q)/(-mu)).__floor__() for k,q in cost.items()}
            core=sum(q*b[i] for i,q in Y.items())
            d2=d/(-mu)-Q(1498,scale) # at most 2*7*107 floors
            ub=core-d2
            if best is None or ub<best:
                best=ub;bu=((core-4092)*scale).__floor__()
                data=json.dumps([{i:str(q) for i,q in Y.items() if q},[[k,q] for k,q in C.items() if q],bu],separators=(',',':'))+'\n'
                Path('target/fifteen_slice.json').write_text(data)
                if ub<4092:
                    d3,_,_=oracle(C,bu,height=15)
                    if core-d3<4092:file.with_name('fifteen_upper_109.json').write_text(data);assert check(15)<4092;return
        add(np.array(sol.col_value)[ci],1)
        if aa:extract(aa,cost)
        if not aa or it%4==0:
            _,_,aa=oracle(cost,budget,'witness',15);extract(aa,cost)

if __name__=='__main__':run()
