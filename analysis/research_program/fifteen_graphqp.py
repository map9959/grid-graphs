"""Small price-correction QP with a path-potential inequality for every sampled arc."""
from .fourteen_bound import *

def run():
    import clarabel as cb
    import numpy as np
    from scipy import sparse
    ns,A,b,obj,l,*_=core15();bl=[(0,9),(6,9)];labs=layout(l,bl);seen=set();bank=[];best=None
    mir={fine_axis(j,15):fine_axis(106-j,15) for j in range(107)}
    flip=lambda k:(mir[k[0]],k[1],((k[2]&73)<<2)|(k[2]&146)|((k[2]&292)>>2))
    rep={k:min(k,flip(k)) for k in l};freq=Counter(rep[h,o+r,m] for o,h,r,m in labs)
    mult=Counter(fine_axis(j,15) for j in range(107))
    _,aa=json.loads(pathspec(15)[1].read_text());arcs={(j,(a,v,tuple(p)),c) for j,(a,v),p,c,_ in aa}
    start=pathspec(15)[0]
    settings=cb.DefaultSettings();settings.verbose=False;settings.max_threads=1;settings.max_iter=200
    args=__import__('sys').argv;three='--three' in args;deep=three or '--deep' in args
    for it in range(120):
        for tag in ('mixqp','aspire','elastic','level','main','trust','master','quadratic','slice','graphqp','deepqp'):
            if tag=='deepqp' and not three:continue
            if tag=='graphqp' and it and not deep:continue
            p=Path('target/fifteen_'+tag+'.json')
            if not p.exists():continue
            text=p.read_text();key=hash(text)
            if key in seen:continue
            seen.add(key);yp,cc,bu=json.loads(text)[:3];y={int(i):Q(q) for i,q in yp.items()};c={tuple(k):q for k,q in cc}
            assert max(projected(A,b,obj,labs,y,{k:Q(q,scale) for k,q in c.items()}).values())<=0
            bank.append((y,c,sum(q*b[i] for i,q in y.items())))
            if not it and tag in (('mixqp','graphqp') if deep else ('mixqp','aspire','elastic','master')):
                res=oracle(c,bu,'witness',15)
                if res:arcs.update(res[2])
        N=len(bank);terms=[];ff={};end=N;active=set()
        for j,s,c in sorted(arcs):
            a,v,p=s;d=v,c,move(v,p,c);assert d[2] is not None
            src=ff.setdefault((j,s),len(ff)+N)
            dst=ff.setdefault((j+1,d),len(ff)+N) if j<108 else -1
            ks=tuple((fine_axis(j-2,15),r,m) for r,m in enumerate(masks(a,v,c,15))) if j>=2 else ()
            reduced=tuple(rep[k] for k in ks);terms.append((src,dst,ks,reduced));active.update(reduced)
        I=N+len(ff);ix={k:I+i for i,k in enumerate(sorted(active))};I+=len(ix)
        # A perturbation is shared among all occurrences of one reflected
        # mask pair. Unseen prices in each orbit absorb the unused total.
        groups=defaultdict(list);missing=Counter();W={};co={}
        for k in set(rep.values()):
            num=1 if k==flip(k) else 2
            if k in active:
                groups[l[k]].append((ix[k],num));W[ix[k]]=num*mult[k[0]]**2;co[k]=ix[k]
            else:missing[l[k]]+=num
        residual={}
        for x,g in groups.items():
            if missing[x]:
                residual[x]=I;g.append((I,missing[x]));W[I]=missing[x];I+=1
        sl=I;I+=1;rs=[];cols=[];vs=[];bb=[]
        def row(entries,rhs):
            j=len(bb);bb.append(rhs)
            for i,w in entries:
                if w:rs.append(j);cols.append(i);vs.append(w)
        row([(i,1) for i in range(N)],1)
        for x,gg in groups.items():row(gg,0)
        eq=len(bb);KM=len(terms);regret=np.empty((N,KM));ub=[]
        for i,(_,prices,rhs) in enumerate(bank):
            table=Counter()
            for (o,h,r,m),q in prices.items():table[h,o+r,m]+=q
            ds=defaultdict(lambda:float('inf'));ds[-1]=0
            for j in reversed(range(KM)):
                src,dst,ks,_=terms[j];q=sum(table[k] for k in ks)/scale+ds[dst]
                ds[src]=min(ds[src],q);regret[i,j]=q
            ub.append(float(rhs)-ds[ff[0,start]])
            for j,(src,_,_,_) in enumerate(terms):regret[i,j]-=ds[src]
        for j,(src,dst,ks,reduced) in enumerate(terms):
            rr=[(i,-q) for i,q in enumerate(regret[:,j])]+[(src,1)]+([(dst,-1)] if dst>=0 else [])
            rr.extend((ix[k],-1) for k in reduced);row(rr,0)
        row([(i,v-(4091.978 if three else 4091.84 if deep else 4091.95)) for i,v in enumerate(ub)]+[(ff[0,start],-1),(sl,-1)],0)
        for i in range(N):row([(i,-1)],0)
        row([(sl,-1)],0)
        diag=np.zeros(I)
        for i,v in W.items():diag[i]=v
        diag[:N]=.00001;q=np.zeros(I);q[sl]=500
        mat=sparse.csc_matrix((vs,(rs,cols)),shape=(len(bb),I))
        solver=cb.DefaultSolver(sparse.diags(diag,format='csc'),q,mat,np.array(bb,dtype=float),[cb.ZeroConeT(eq),cb.NonnegativeConeT(len(bb)-eq)],settings)
        sol=solver.solve();print('graph QP',it,KM,N,sol.status,'slack',sol.x[sl],flush=True)
        assert str(sol.status) in ('Solved','AlmostSolved','InsufficientProgress')
        weights=[Q(max(0,v)).limit_denominator(10**5) for v in sol.x[:N]];weights=[v/sum(weights) for v in weights]
        Y=Counter();C=Counter();rhs=0
        for w,(y,c,rr) in zip(weights,bank):
            if not w:continue
            rhs+=w*rr
            for i,z in y.items():Y[i]+=w*z
            for k,z in c.items():C[k]+=w*z
        cost={}
        for k,x in labs.items():
            o,h,r,m=k;g=rep[h,o+r,m];jj=ix.get(g,residual.get(x))
            dz=0 if jj is None else (1 if g==flip(g) else 2)*sol.x[jj]/freq[g]
            cost[k]=C[k].__floor__()+round(dz*scale)
        rc=projected(A,b,obj,labs,Y,{k:Q(v,scale) for k,v in cost.items()})
        for k,x in labs.items():
            if rc[x]>0:
                z=-((-rc[x]*scale).__floor__());cost[k]-=z;rc[x]-=Q(z,scale)
        assert max(rc.values())<=0
        bu=((rhs-4092)*scale).__floor__();d,n,aa=oracle(cost,bu,'threepaths' if three else 'paths',15);v=rhs-d
        print('price upper',float(v),'arcs',len(aa),flush=True)
        if best is None or v<best:
            best=v;data=json.dumps([{i:str(q) for i,q in Y.items() if q},[[k,q] for k,q in cost.items() if q],bu],separators=(',',':'))+'\n'
            Path('target/fifteen_'+('threeqp' if three else 'deepqp' if deep else 'graphqp')+'.json').write_text(data)
            if v<4092:
                if three:
                    assert oracle(cost,bu,'three',15)[0]>Q(bu,scale)
                    file.with_name('fifteen_upper_109.json').write_text(data)
                    assert check(15,mode='three')<4092
                else:file.with_name('fifteen_upper_109.json').write_text(data);assert check(15)<4092
                return
        arcs.update(aa);res=oracle(cost,bu,'witness',15)
        if res:arcs.update(res[2])

if __name__=='__main__':run()
