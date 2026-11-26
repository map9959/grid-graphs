"""Pooled transfer of complete directed-star assignments in diagonal boundary strips."""
from .diagonal_strip import relaxation,move,masks,Counter,defaultdict,MASKS,SYM,trans,lru_cache,product
from .chart_counts import count
from .repeating_patch_dual import Path,json,Q
import sys

@lru_cache(None)
def assign(b,west,forced,H):
    # west is the set of current vertices already pointing left.
    ds=[2 if west>>i&1 else -1 for i in range(H)];ans=[]
    def vertical(i):
        if i+1==H:
            avail=forced&sum(1<<i for i,x in enumerate(ds) if x<0);v=avail
            while True:
                dirs=tuple(0 if v>>i&1 else z for i,z in enumerate(ds))
                ans.append((forced^v,dirs))
                if not v:break
                v=(v-1)&avail
        elif b>>i&3:
            for t,d in ((i,1),(i+1,3)):
                if ds[t]<0:ds[t]=d;vertical(i+1);ds[t]=-1
        else:vertical(i+1)
    vertical(0);return ans

def run(n,H,d,w):
    import highspy as hs
    import numpy as np
    base=43+(n-43)%6;ns,rows,obj=relaxation(base,d+4,pooled=d,period=3,diagonal=w)
    inv={x:key for key,x in ns.items()}
    def pt(i,j,S,h):
        ax=lambda a:a if a<h else 2*h+3+a-S if a>=S-h else h+(a-h)%3
        clip=lambda a:max(-w-5,min(w+5,a))
        return ax(i),ax(j),clip(i-j),clip(i+j+1-S)
    def loc(i,j,S,h):return tuple(pt(a,b,S,h) for g in range(8) for a,b in [trans(i,j,S,g)])
    coef=[];ops=[];xs=list(inv);ix={x:i for i,x in enumerate(xs)}
    h=hs.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
    h.setOptionValue('solver','ipm');h.setOptionValue('run_crossover','off')
    h.addVars(len(xs),np.zeros(len(xs)),np.full(len(xs),hs.kHighsInf));h.setMaximize();h.changeColsCost(len(xs),np.arange(len(xs)),[obj.get(x,0) for x in xs])
    def row(a,b,cs=()):
        i=h.getNumRow();h.addRow(float(a),float(b),len(cs),[i for i,z in cs],[float(z) for i,z in cs]);return i
    I=hs.kHighsInf
    for cs,op,b0 in rows:
        val=(b0,0,0)
        if b0>0 and op=='=':
            k,atom=inv[cs[0][0]];p=int(k=='p');val=count(n-2*p,d+4-p,w+5,atom[0])
        b=val[0];coef.append(val);ops.append(op);row(b if op!='<=' else -I,b if op!='>=' else I,[(ix[x],v) for x,v in cs])
    north_cut='--north-cut' in sys.argv
    if north_cut:
        from .sector_track_support import support,layer
        assert (d,w)==(2,2) and n>=67
        allowed=support(n);r=4 if n%6==1 else 3
        sets=allowed[r][18:21];assert not layer(tuple(sets))
        costs=Counter()
        for j,words in enumerate(sets,18):
            img=loc(r,j,n-2,d+3)
            for m in MASKS:
                if m not in words:costs[ix[ns['p',min(zip(img,SYM[m]))]]]+=1
        # Each of k-12 disjoint triples of patch origins contributes
        # at least once. The RHS grows by two per six-side increment.
        rhs=n//3-12;coef.append((rhs,2,0));ops.append('>=');row(rhs,I,list(costs.items()))
    labels={}
    def bind(k,x):
        if k not in labels:labels[k]=row(0,0,[(ix[x],-1)])
        return labels[k]
    @lru_cache(None)
    def pl(r,j,m):
        p=loc(r,j,n-2,d+3);return bind(('p',r,p[0],m),ns['p',min(zip(p,SYM[m]))])
    @lru_cache(None)
    def sl(r,j,f,nb,out):
        p=loc(r,j,n,d+4);imgs=[]
        for g in range(8):
            turn=lambda q:((2-q if g&4 else q)+g%4)%4
            word=[9]*4
            for a,z in enumerate(nb):word[turn(a)]=z
            imgs.append((p[g],f,tuple(word),turn(out) if out>=0 else -1))
        return bind(('s',r,p[0],f,nb,out),ns['s',min(imgs)])
    depth=max(d+6,w+H+8);ph=lambda j:j if j<depth else 2*depth+3+j-n if j>=n-depth else depth+(j-depth)%3
    cuts='--lift-cuts' in sys.argv
    fixed_test='--fixed-lift' in sys.argv or cuts
    if fixed_test:
        assert H==3
        source=Path(__file__).with_name(f'oriented_strip_3_{d}_{w}_{n}_flows.json')
        fixed=[{int(i):Q(z) for i,z in m.items()} for m in json.loads(source.read_text())]
        from .strip_extension import collect
        ext=[]
    @lru_cache(None)
    def flow(ph,s):return row(0,0)
    @lru_cache(None)
    def transitions(s,final):
        a,b,P,west=s;out=[]
        for c in ([0] if final else range(1<<H)):
            part=move(b,P,c) if not final else P
            if part is None:continue
            join=0 if final else (b|c);mm=masks(a,b,c,H)
            for right,ds in assign(b,west,join,H):out.append(((b,c,part,right),mm,ds))
        return out
    norm=row(1,1);states=set()
    for b in range(1<<H):
        P=move(0,tuple(range(H)),b);s=(0,b,P,0);states.add(s)
        h.addCol(0,0,I,2,[norm,flow(ph(0),s)],[1,-1])
    seen=set();stage_sources={};norms=[];cnt=Counter((ph(j),ph(j+1) if j+1<n else -1) for j in range(n))
    for j in range(n):
        current=ph(j);nxt=ph(j+1) if j+1<n else -1;key=current,nxt
        if key in seen:continue
        # The first occurrence of a periodic stage may have fewer reachable
        # states than later ones. Start from the complete reachable closure.
        if j==depth:
            while True:
                nxtstates={u for s in states for u,_,_ in transitions(s,False)}
                if nxtstates==states:break
                states|=nxtstates
                if nxtstates<=states and all(u in states for s in states for u,_,_ in transitions(s,False)):break
        seen.add(key);stage_sources[key]=states.copy();nr=row(cnt[key],cnt[key]);norms.append((nr,key,cnt[key]))
        dest=set();offset=[];cols=[];ww=[]
        for s in sorted(states):
            a,b,P,west=s;src=flow(current,s)
            for u,ms,ds in transitions(s,nxt<0):
                if fixed_test:
                    col=h.getNumCol()+len(offset)
                    if any(col in x for x in fixed):
                        ext.append((col,collect(n,j,s,u,ds,loc,ns,ix,d)))
                c=u[1];ids=[src,nr];weights=[1.,1.]
                if nxt>=0:ids.append(flow(nxt,u));weights.append(-1.);dest.add(u)
                if 0<j<n-1:ids.extend(pl(r,j-1,m) for r,m in enumerate(ms));weights.extend([1.]*(H-2))
                for r in range(H-1):
                    nb=(c>>r&1 if nxt>=0 else 9,b>>(r+1)&1,a>>r&1 if j else 9,b>>(r-1)&1 if r else 9)
                    ids.append(sl(r,j,b>>r&1,nb,ds[r]));weights.append(1.)
                offset.append(len(cols));cols.extend(ids);ww.extend(weights)
        E=len(offset);h.addCols(E,np.zeros(E),np.zeros(E),np.full(E,I),len(cols),np.array(offset,dtype=np.int32),np.array(cols,dtype=np.int32),np.array(ww))
        states=dest
    print('oriented',H,'side',n,'model',h.getNumCol(),'columns',h.getNumRow(),'rows',flush=True)
    if fixed_test:
        from .strip_extension import report,lift_cuts
        if not cuts:report(n,fixed,ext);return
        for i,js in lift_cuts(fixed,ext):
            row(-I,0,[(i,1)]+[(j,-1) for j in js])
    cert=Path(__file__).with_name(f'oriented_strip_{H}_{d}_{w}_{n}'+('_cuts' if cuts else '')+('_northcut' if north_cut else '')+'.json')
    h.ensureColwise()
    if any(x in sys.argv for x in ('--exact','--replay','--moments','--check-moments')):
        # Check that every physical stage (including repeated stages)
        # maps to the same chart labels and is covered by the pooled arcs.
        st0={(0,b,move(0,tuple(range(H)),b),0) for b in range(1<<H)}
        signatures={};covered={}
        for N in (n,n+6):
            phN=lambda j:j if j<depth else 2*depth+3+j-N if j>=N-depth else depth+(j-depth)%3
            st=st0
            for j in range(N):
                k=phN(j),phN(j+1) if j+1<N else -1
                sig=tuple(loc(r,j,N,d+4) for r in range(H-1))
                if 0<j<N-1:sig+=tuple(loc(r,j-1,N-2,d+3) for r in range(H-2))
                assert signatures.setdefault(k,sig)==sig
                assert st<=stage_sources[k]
                if k in covered and st==covered[k][0]:st=covered[k][1]
                else:
                    nxt={u for s in st for u,_,_ in transitions(s,k[1]<0)}
                    covered[k]=st,nxt;st=nxt
        for p in (0,1):
            S=n-2*p;cells=Counter(pt(i,j,S,d+4-p) for i,j in product(range(S),repeat=2))
            total=[0]*3
            for cell,v in cells.items():
                q=count(S,d+4-p,w+5,cell);assert q[0]==v
                for j in range(3):total[j]+=q[j]
            assert total==[S*S,12*S+36,72]
        for j in range(depth,depth+3):
            src=stage_sources[j,ph(j+1)]
            assert all(u in stage_sources[ph(j+1),ph(j+2)] for s in src for u,_,_ in transitions(s,False))
    if '--moments' in sys.argv or '--check-moments' in sys.argv:
        witness=cert.with_name(cert.stem+'_flows.json')
        vals=[] if '--moments' in sys.argv else json.loads(witness.read_text())
        h.setOptionValue('solver','simplex')
        for j in range(3):
            for i,(v,op) in enumerate(zip(coef,ops)):
                h.changeRowBounds(i,v[j] if op!='<=' else -I,v[j] if op!='>=' else I)
            h.changeRowBounds(norm,int(j==0),int(j==0))
            for i,(a,b),z in norms:
                value=(z,2*int(depth<=a<depth+3 and depth<=b<depth+3),0)[j];h.changeRowBounds(i,value,value)
            if '--moments' in sys.argv:
                h.run();assert h.getModelStatus()==hs.HighsModelStatus.kOptimal
                x={i:Q(z).limit_denominator(100000) for i,z in enumerate(h.getSolution().col_value) if abs(z)>1e-8}
            else:x={int(i):Q(s) for i,s in vals[j].items()}
            lp=h.getLp();M=lp.a_matrix_;s,idx,v=M.start_,M.index_,M.value_
            bal=Counter()
            for col,z in x.items():
                assert z>=0
                for a in range(s[col],s[col+1]):bal[idx[a]]+=int(v[a])*z
            for i,(a,b) in enumerate(zip(lp.row_lower_,lp.row_upper_)):
                assert a<=-I or bal[i]>=int(a),(i,bal[i],a)
                assert b>=I or bal[i]<=int(b),(i,bal[i],b)
            c=lp.col_cost_;score=sum(int(c[i])*z for i,z in x.items())
            print('exact feasible moment',j,'support',len(x),'score',score,flush=True)
            if '--moments' in sys.argv:vals.append({i:str(z) for i,z in x.items()})
        if '--moments' in sys.argv:witness.write_text(json.dumps(vals,separators=(',',':'))+'\n')
        return
    if '--exact' in sys.argv:
        # Search the dual directly with the desired three coefficients
        # imposed simultaneously. L1 minimization favors sparse rationals.
        from scipy.sparse import csc_matrix,csr_matrix
        from scipy.optimize import linprog
        lp=h.getLp();M=lp.a_matrix_;N=h.getNumRow();J=h.getNumCol()
        A=csc_matrix((M.value_,M.index_,M.start_),shape=(N,J)).T
        rhs=np.zeros((3,N));rhs[:,:len(coef)]=np.asarray(coef).T;rhs[0,norm]=1
        for i,(a,b),z in norms:
            rhs[0,i]=z;rhs[1,i]=2*(depth<=a<depth+3 and depth<=b<depth+3)
        k=n//3;target=[3*k*k+16*k/3-7/6,12*k+12+32/3,24]
        from scipy.sparse import hstack
        B=csr_matrix(rhs)
        r=linprog(np.ones(2*N),A_ub=hstack((-A,A)),b_ub=-np.array(lp.col_cost_),
                  A_eq=hstack((B,-B)),b_eq=target,
                  bounds=[(0,0 if v>=I else None) for v in lp.row_upper_]+[(0,0 if v<=-I else None) for v in lp.row_lower_],
                  method='highs-ds',options={'threads':1})
        assert r.success,r.message
        from .repeating_patch_dual import recover
        raw={i:Q(z) for i,z in enumerate(r.x[:N]-r.x[N:]) if abs(z)>1e-8}
        # Tight inequalities form rational linear equations. Include
        # the demanded RHS moments as extra tight columns.
        ext=hstack((A.T,B.T)).tocsr()
        tar=Counter({i:Q(int(x)) for i,x in enumerate(lp.col_cost_) if x})
        for j,z in enumerate(target):tar[J+j]=Q(z).limit_denominator(6)
        mat=[([], '=') for _ in range(N)]
        for i in raw:
            lo,hi=ext.indptr[i:i+2]
            mat[i]=([(int(j),int(v)) for j,v in zip(ext.indices[lo:hi],ext.data[lo:hi])],'=')
        y=recover(mat,tar,raw)
    elif '--replay' in sys.argv:
        saved=json.loads(cert.read_text());y={int(i):Q(z) for i,z in saved.items()}
    else:
        h.run();print('status',h.getModelStatus(),'candidate',h.getObjectiveValue(),flush=True)
        assert h.getModelStatus()==hs.HighsModelStatus.kOptimal
    if '--replay' in sys.argv or '--exact' in sys.argv:
        # Retrieve the integer columns only. The replay never calls solve.
        lp=h.getLp();a=lp.a_matrix_;assert 'Colwise' in str(a.format_)
        for i,z in y.items():
            assert 0<=i<h.getNumRow()
            if lp.row_lower_[i]<=-I:assert z>=0
            if lp.row_upper_[i]>=I:assert z<=0
        from math import lcm
        den=lcm(*(z.denominator for z in y.values()));Y=[int(y.get(i,0)*den) for i in range(h.getNumRow())]
        starts,values,indices=a.start_,a.value_,a.index_
        for j,c in enumerate(lp.col_cost_):
            s=0
            for k in range(starts[j],starts[j+1]):
                v=values[k];assert int(v)==v;s+=Y[indices[k]]*int(v)
            assert c==int(c) and s>=int(c)*den,(j,s,c,den)
        poly=[sum(y.get(i,0)*v[j] for i,v in enumerate(coef)) for j in range(3)]
        poly[0]+=y.get(norm,0)
        for i,(a,b),z in norms:
            poly[0]+=y.get(i,0)*z
            if depth<=a<depth+3 and depth<=b<depth+3:poly[1]+=2*y.get(i,0)
        print('exact joint Newton',*poly,'denominator',den,flush=True)
        if '--exact' in sys.argv:cert.write_text(json.dumps({i:str(z) for i,z in y.items()},separators=(',',':'))+'\n')
        return
    if h.getModelStatus()==hs.HighsModelStatus.kOptimal:
        yy=h.getSolution().row_dual
        poly=[sum(z*v[j] for z,v in zip(yy,coef)) for j in range(3)]
        poly[0]+=yy[norm]
        for i,(a,b),z in norms:
            poly[0]+=yy[i]*z
            if depth<=a<depth+3 and depth<=b<depth+3:poly[1]+=2*yy[i]
        print('discovery Newton',poly,flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:5]))
