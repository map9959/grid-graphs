"""Sparse proximal path master for the joint 15-row relaxation."""
from .fourteen_bound import *

def run():
    import numpy as np
    from scipy import sparse
    import clarabel as cb
    ns,A,b,obj,l,*_=core15();bl=[(0,9),(6,9)];labs=layout(l,bl);start=pathspec(15)[0]
    yy,cc,_=json.loads(Path('target/fifteen_mixqp.json').read_text());Y={int(i):Q(q) for i,q in yy.items()};C={tuple(k):q for k,q in cc}
    # Exact equalities x_parent=x_child permit elimination for discovery.
    # Record the row and pivot sign so every core multiplier lifts back.
    parent={};edges=[];norm={};agg=[]
    def root(x):
        while x in parent:x=parent[x]
        return x
    for i,((cs,op),v) in enumerate(zip(A,b)):
        if v>0 and op=='=' and all(a>0 for x,a in cs):
            for x,a in cs:norm[x]=i,a
        if not v and any(x[0] in 'fghij' and a>0 for x,a in cs) and len({x[0] for x,a in cs})>1:agg.append((i,cs))
        if op=='=' and v==0 and len(cs)==2 and {q for x,q in cs}=={-1,1}:
            (x,a),(z,_) =cs;u,w=root(x),root(z)
            if u!=w:edges.append((i,u,w,a));parent[u]=w
    xs=sorted({root(x) for x in ns.values()});ix={x:i for i,x in enumerate(xs)};N=len(xs)
    eq=[];ineq=[];seen=set()
    for i,((cs,op),v) in enumerate(zip(A,b)):
        row=Counter()
        for x,a in cs:row[ix[root(x)]]+=a
        row=tuple(sorted((x,a) for x,a in row.items() if a));key=row,op,v
        if row and key not in seen:
            seen.add(key);(eq if op=='=' else ineq).append((i,row,1 if op!='>=' else -1))
    mir={fine_axis(j,15):fine_axis(106-j,15) for j in range(107)}
    def mirror(k):
        h,r,m=k;return mir[h],r,((m&73)<<2)|(m&146)|((m&292)>>2)
    rep={k:min(k,mirror(k)) for k in l};keys=sorted(set(rep.values()));ki={k:i for i,k in enumerate(keys)}
    mult=Counter(fine_axis(j,15) for j in range(107));freq=Counter(rep[h,o+r,m] for o,h,r,m in labs)
    def center(Y,C):
        ct=np.zeros(len(keys))
        for (o,h,r,m),q in C.items():ct[ki[rep[h,o+r,m]]]+=q/scale
        return ct
    cen=center(Y,C);words={};rng=np.random.default_rng(115)
    def add(w):
        w=min(tuple(w),tuple(reversed(w)))
        if w in words:return
        ct=Counter()
        for j in range(107):
            h=fine_axis(j,15)
            for r,m in enumerate(masks(*w[j:j+3],15)):
                k=rep[h,r,m];ct[ki[k]]+=1 if k==mirror(k) else .5
        words[w]=ct
    _,aa=json.loads(pathspec(15)[1].read_text());f=defaultdict(dict)
    for j,(a,v),p,c,q in aa:f[j,(a,v,tuple(p))][c]=Q(q)
    while f[0,start]:
        s=start;w=[];ps=[]
        for j in range(109):
            c=next(iter(f[j,s]));ps.append((j,s,c));w.append(c);s=s[1],c,move(s[1],s[2],c)
        z=min(f[j,s][c] for j,s,c in ps)
        for j,s,c in ps:
            f[j,s][c]-=z
            if not f[j,s][c]:del f[j,s][c]
        add(w)
    def extract(aa,cost):
        g=defaultdict(list)
        for j,s,c in aa:g[j].append((s,c))
        dp={start:0};hist=[]
        for j in range(109):
            pr={};nd={};h=fine_axis(j-2,15)
            for s,c in g[j]:
                if s not in dp:continue
                a,v,p=s;d=v,c,move(v,p,c);z=dp[s]
                if j>=2:
                    ms=masks(a,v,c,15);z+=sum(cost.get((o,h,r,m),0) for o,_ in bl for r,m in enumerate(ms[o:o+7]))
                if d not in nd or z<nd[d]:nd[d]=z;pr[d]=s,c
            dp=nd;hist.append(pr)
        for d in sorted(dp,key=dp.get)[:160]:
            w=[]
            for pr in reversed(hist):d,c=pr[d];w.append(c)
            add(w[::-1])
    for tag in ('mixqp','elastic','box','main','aspire'):
        _,cc,bu=json.loads(Path('target/fifteen_'+tag+'.json').read_text())[:3];c={tuple(k):q for k,q in cc}
        _,_,aa=oracle(c,bu,'witness',15);extract(aa,c)
    M=len(keys);nc=N+M;ct=Counter()
    for x,q in obj.items():ct[ix[root(x)]]+=q
    qbase=np.array([-ct[i] for i in range(N)]+[0.]*M)
    settings=cb.DefaultSettings();settings.verbose=False;settings.max_threads=1;settings.max_iter=300
    best=None
    for it in range(160):
        K=len(words);sl=nc+K;names=sl+len(eq)+len(ineq);rs=[];cols=[];vs=[];bb=[];maps=[]
        def row(cs,v):
            j=len(bb);bb.append(v)
            for x,w in cs:rs.append(j);cols.append(x);vs.append(w)
        for i,cs,sgn in eq:
            t=len(maps);maps.append((i,sgn,len(bb)));row(list(cs)+[(sl+t,1)],b[i])
        row([(nc+k,1) for k in range(K)],1)
        links=len(bb)
        for j,k in enumerate(keys):row([(N+j,-1),(ix[root(l[k])],-1)],0)
        for k,ct0 in enumerate(words.values()):
            for j,w in ct0.items():rs.append(links+j);cols.append(nc+k);vs.append(w)
        neq=len(bb)
        for i,cs,sgn in ineq:
            t=len(maps);maps.append((i,sgn,len(bb)));row([(x,a*sgn) for x,a in cs]+[(sl+t,1)],b[i]*sgn)
        for j in range(N):row([(j,-1)],0)
        for k in range(K):row([(nc+k,-1)],0)
        mat=sparse.csc_matrix((vs,(rs,cols)),shape=(len(bb),names))
        q=np.r_[qbase[:N],cen,np.zeros(K),[-float(Y.get(i,0))*sgn for i,sgn,j in maps]]
        # Link residual e=word mass-core mass; dual price = center+penalty*e.
        rate=float(__import__('os').environ.get('PRICE_RATE','2.5'))
        P=sparse.diags(np.r_[np.zeros(N),[rate/mult[k[0]]**2 for k in keys],np.zeros(K),np.ones(len(maps))*.25],format='csc')
        solver=cb.DefaultSolver(P,q,mat,np.array(bb,dtype=float),[cb.ZeroConeT(neq),cb.NonnegativeConeT(len(bb)-neq)],settings)
        sol=solver.solve();print('QP',it,K,sol.status,-sol.obj_val,flush=True)
        assert str(sol.status) in ('Solved','AlmostSolved','InsufficientProgress')
        raw=sol.z;y={i:Q(round(raw[j]*scale),scale)*sgn for i,sgn,j in maps if abs(raw[j])>1e-10}
        c={}
        for k,x in labs.items():
            o,h,r,m=k;g=rep[h,o+r,m];j=ki[g]
            c[k]=C.get(k,0)+round((raw[links+j]-cen[j])*scale/freq[g])
        # Satisfy the eliminated columns bottom-up. Edges store original
        # row endpoints, which need not have been roots at elimination time.
        rc=projected(A,b,obj,labs,y,{k:Q(q,scale) for k,q in c.items()})
        sums=rc.copy()
        for i,u,w,a in edges:sums[w]+=sums[u]
        for i,u,w,a in reversed(edges):
            terms=A[i][0];z=Q(sums[u])/a
            y[i]=y.get(i,0)+z
            # Update all affected subtree sums; the eliminated row is
            # anchored at its actual endpoints, not arbitrary representatives.
            for x,t in terms:
                while True:
                    sums[x]-=z*t
                    if x not in parent:break
                    x=parent[x]
        rc=projected(A,b,obj,labs,y,{k:Q(v,scale) for k,v in c.items()})
        for i,cs in reversed(agg):
            z=max([rc[x]/w for x,w in cs if w>0 and x not in norm]+[0])
            if z>0:
                y[i]=y.get(i,0)+z
                for x,w in cs:rc[x]-=w*z
        adj=Counter()
        for x,z in rc.items():
            if z>0:
                i,w=norm[x];adj[i]=max(adj[i],z/w)
        for i,z in adj.items():y[i]=y.get(i,0)+z
        assert max(projected(A,b,obj,labs,y,{k:Q(v,scale) for k,v in c.items()}).values())<=0
        rhs=sum(q*b[i] for i,q in y.items());budget=((rhs-4092)*scale).__floor__()
        d,n,aa=oracle(c,budget,'paths',15);ub=rhs-d
        print('priced',float(ub),'exact arcs',len(aa),flush=True)
        if best is None or ub<best:
            best=ub;Y=y;C=c;cen=center(Y,C)
            data=json.dumps([{i:str(q) for i,q in y.items() if q},[[k,q] for k,q in c.items() if q],budget],separators=(',',':'))+'\n'
            Path('target/fifteen_quadratic.json').write_text(data)
            if ub<4092:file.with_name('fifteen_upper_109.json').write_text(data);assert check(15)<4092;return
        if aa:extract(aa,c)
        _,_,aa=oracle(c,budget,'witness',15);extract(aa,c)

if __name__=='__main__':run()
