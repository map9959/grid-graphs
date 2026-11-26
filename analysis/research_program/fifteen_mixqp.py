"""A convex combination of core duals, with a minimum-norm event-price correction."""
from .fourteen_bound import *

def run():
    import numpy as np
    from scipy import sparse
    import osqp
    _,A,b,obj,l,*_=core15();bl=[(0,9),(6,9)];labs=layout(l,bl);keys=list(labs);idx={k:i for i,k in enumerate(keys)}
    ids={x:i for i,x in enumerate(sorted(set(labs.values())))};group=np.array([ids[labs[k]] for k in keys])
    count=np.bincount(group);ph=Counter(fine_axis(j,15) for j in range(107));wt=np.array([1/ph[k[1]] for k in keys])
    mir={fine_axis(j,15):fine_axis(106-j,15) for j in range(107)}
    rf=[idx[o,mir[h],r,((m&73)<<2)|(m&146)|((m&292)>>2)] for o,h,r,m in keys]
    assert np.all(group[rf]==group)
    def proj(v):
        v=.5*(v+v[rf]);return v-np.bincount(group,weights=v)[group]/count[group]
    bank=[];seen=set();words=set();events=[];normals=[];start=pathspec(15)[0]
    def add(w):
        w=min(tuple(w),tuple(reversed(w)))
        if w in words:return
        words.add(w);v=np.zeros(len(keys))
        for j in range(107):
            ms=masks(*w[j:j+3],15)
            for o,_ in bl:
                for r,m in enumerate(ms[o:o+7]):v[idx[o,fine_axis(j,15),r,m]]+=1
        v=.5*(v+v[rf]);events.append(v);normals.append(proj(v)*wt)
    def extract(aa,cost):
        import random
        rng=random.Random(15+len(words));layers=defaultdict(list)
        for j,s,c in aa:layers[j].append((s,c))
        start=pathspec(15)[0];dp={start:0};hist0=[]
        for j in range(109):
            pr={};nd={};h=fine_axis(j-2,15)
            for s,c0 in layers[j]:
                if s not in dp:continue
                a,v,p=s;d=v,c0,move(v,p,c0);z=dp[s]
                if j>=2:
                    ms=masks(a,v,c0,15);z+=sum(cost.get((o,h,r,m),0) for o,_ in bl for r,m in enumerate(ms[o:o+7]))
                if d not in nd or z<nd[d]:nd[d]=z;pr[d]=s,c0
            dp=nd;hist0.append(pr)
        for d in sorted(dp,key=dp.get)[:24]:
            w=[]
            for pr in reversed(hist0):d,c0=pr[d];w.append(c0)
            add(tuple(reversed(w)))
        # Min conditional suffix through each discovered arc.
        hist=[];val={}
        for j in reversed(range(109)):
            ns=defaultdict(list);h=fine_axis(j-2,15)
            for s,c0 in layers[j]:
                a,v,p=s;dst=v,c0,move(v,p,c0)
                if j<108 and dst not in val:continue
                z=val.get(dst,0)
                if j>=2:
                    ms=masks(a,v,c0,15);z+=sum(cost.get((o,h,r,m),0) for o,_ in bl for r,m in enumerate(ms[o:o+7]))
                ns[s].append((z,c0,dst))
            for opts in ns.values():opts.sort()
            hist.append(ns);val={s:opts[0][0] for s,opts in ns.items()}
        for i in range(90):
            s=start;w=[]
            for choices in reversed(hist):
                opts=choices[s];lim=opts[0][0]+(scale*(i%5)/200 if i else 0)
                z,c0,s=rng.choice([o for o in opts if o[0]<=lim]);w.append(c0)
            add(w)
    best=None;G=np.zeros((0,0))
    for it in range(90):
        for tag in ('mixqp','balanced','aspire','elastic','level','main','box','trust','feature_candidate','reflect','slice'):
            if tag=='mixqp' and it!=0:continue
            fn=Path('target/fifteen_'+tag+'.json')
            if not fn.exists():continue
            text=fn.read_text();key=hash(text)
            if key in seen:continue
            seen.add(key);yy,cc,bu=json.loads(text)[:3];y={int(i):Q(q) for i,q in yy.items()};c={tuple(k):v for k,v in cc}
            assert max(projected(A,b,obj,labs,y,{k:Q(q,scale) for k,q in c.items()}).values())<=0
            bank.append((y,c,sum(q*b[i] for i,q in y.items()),np.array([c.get(k,0)/scale for k in keys])))
        N=len(bank)
        if it==0:
            for i in (0,1,N-1):
                _,c,rhs,cv=bank[i];_,_,aa=oracle(c,((rhs-4092)*scale).__floor__(),'witness',15);extract(aa,c)
        m=len(normals);K=len(G);P=np.array(normals)
        if K<m:
            z=P[K:]@P.T;gg=np.empty((m,m));gg[:K,:K]=G;gg[K:,:]=z;gg[:,K:]=z.T;G=gg
        vals,U=np.linalg.eigh(G);ok=vals>1e-8;L=U[:,ok]*np.sqrt(vals[ok]);n=L.shape[1]
        # cost perturbation has Euclidean norm ||z|| in an orthonormal
        # basis of the projected keyword counts. Each row enforces a word.
        F=np.stack([float(rhs)-4091.93-np.dot(events,cv) for _,_,rhs,cv in bank],axis=1)
        C=sparse.vstack([sparse.csc_matrix(np.column_stack((L,-F))),sparse.hstack([sparse.csc_matrix((N,n)),sparse.eye(N)]),sparse.csc_matrix(np.r_[np.zeros(n),np.ones(N)][None,:])],format='csc')
        opt=osqp.OSQP();opt.setup(P=sparse.diags(np.r_[np.ones(n),np.full(N,.0001)],format='csc'),q=np.zeros(n+N),A=C,l=np.r_[np.zeros(m+N),1.],u=np.r_[np.full(m+N,np.inf),1.],verbose=False,eps_abs=1e-6,eps_rel=1e-6,max_iter=60000)
        sol=opt.solve()
        if sol.info.status_val not in (1,2):print('QP status',sol.info.status,flush=True);return
        weights=[Q(max(0,float(q))).limit_denominator(1000000) for q in sol.x[n:]];weights=[q/sum(weights) for q in weights]
        correction=proj(((U[:,ok]@(sol.x[:n]/np.sqrt(vals[ok])))@P)*wt)
        Y=Counter();C=Counter();rhs=0
        for q,(y,c,v,cv) in zip(weights,bank):
            if not q:continue
            rhs+=q*v
            for i,s in y.items():Y[i]+=q*s
            for k,s in c.items():C[k]+=q*s
        cost={k:(C[k]+Q(round(correction[i]*scale*1000),1000)).__floor__() for i,k in enumerate(keys)}
        rc=projected(A,b,obj,labs,Y,{k:Q(q,scale) for k,q in cost.items()})
        for k,x in labs.items():
            if rc[x]>0:
                q=-((-rc[x]*scale).__floor__());cost[k]-=q;rc[x]-=Q(q,scale)
        assert max(rc.values())<=0
        budget=((rhs-4092)*scale).__floor__();d,n,aa=oracle(cost,budget,'paths',15);ub=rhs-d
        print(it,'bank',N,'words',m,'upper',float(ub),'arcs',len(aa),flush=True)
        if best is None or ub<best:
            best=ub;data=json.dumps([{i:str(q) for i,q in Y.items() if q},[[k,q] for k,q in cost.items() if q],budget],separators=(',',':'))+'\n'
            Path('target/fifteen_mixqp.json').write_text(data)
            if ub<4092:file.with_name('fifteen_upper_109.json').write_text(data);assert check(15)<4092;return
        if aa:extract(aa,cost)
        if not aa or m==len(words):
            _,_,aa=oracle(cost,budget,'witness',15);extract(aa,cost)

if __name__=='__main__':run()
