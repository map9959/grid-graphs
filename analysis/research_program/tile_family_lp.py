"""A size-independent plaquette-count relaxation for a fixed NW frame and star.

Only the counts on normalization rows depend on k. The overlap equations
sum both sides of the very same physical seams. No uniformity of marks
within a type is assumed.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
from fractions import Fraction
import gzip,json,sys
from .defect_window import table,window,DIR
from .slit_star_transfer import frame_path

L=6
def typ(i,K):
    return i if i<L else 2*L+1+i-K if i>=K-L else L

def projected(w,starcol=5):
    from pysat.solvers import Solver
    n=119;k=(n-2)//3;K=k-1;T=table(n);marks,path=frame_path(n,w)
    assert starcol in (5,11)
    target=Path(f'target/tile_family_{w}_{starcol}_h6.json.gz')
    if target.exists():return {tuple(row[:2]):[tuple(b) for b in row[2]] for row in json.loads(gzip.decompress(target.read_bytes()))}
    reps={}
    for p in product(range(K),repeat=2):reps[tuple(typ(i,K) for i in p)]=p
    blocks={}
    for (u,v),(i,j) in sorted(reps.items()):
        x,y=1+3*i,1+3*j
        dom=set(product(range(max(0,x-6),min(n,x+12)),range(max(0,y-6),min(n,y+12))))
        star=(2,starcol);want=all((star[0]+a,star[1]+b) in dom for a,b in ((0,0),*DIR))
        def emit(f,bit,flags):
            for p in dom:
                if p in marks:f.append([bit(*p)*(1 if marks[p] else -1)])
            tiles=[[bit(x+3*a+h,y+3*b+l) for h,l in product(range(3),repeat=2)] for a,b in product(range(2),repeat=2)]
            out=[]
            with Solver(name='cadical195',bootstrap_with=f.clauses) as sol:
                while sol.solve():
                    m=set(sol.get_model());out.append(tuple(sum((z in m)<<h for h,z in enumerate(t)) for t in tiles))
                    sol.add_clause([-z if z in m else z for t in tiles for z in t])
            blocks[u,v]=sorted(out)
        window(n,'rim',1,T,want=want,defects={('s',*star)},root_site=(n-1,n-1),orient=path,domain=dom,emit=emit)
    target.write_bytes(gzip.compress(json.dumps([[*p,b] for p,b in sorted(blocks.items())],separators=(',',':')).encode(),mtime=0))
    return blocks

def solve(w,axis,starcol=5):
    import highspy as hp
    B=projected(w,starcol);n=119;k=(n-2)//3;K=k-1
    reps={tuple(typ(i,K) for i in p):p for p in product(range(K),repeat=2)}
    atoms=[];eqs={};norm={}
    def seam(i,K):
        # No split of the middle columns by which one is first/last.
        h=L-1
        return i if i<h else 2*h+1+i-K if i>=K-h else h
    def integral_counts(k):
        K=k-1;mult=[1]*L+[K-2*L]+[1]*L
        return [mult[u]*mult[v] for u,v in sorted(B)]
    allowed=None
    if '--ports' in sys.argv:
        from .tile_flux_closure import ports,enumerate_blocks,closure
        T=table(n);pp={(dd,f):ports(T,dd,f,False) for dd,f in product(range(2),repeat=2)}
        place=None if starcol==5 else (0,0)
        allowed=set(closure([b for b in enumerate_blocks(0) if all(not(m&16 and m&(40 if axis==1 else 130)) for m in b)],pp,place))
    for p,words in sorted(B.items()):
        i,j=reps[p];u,v=p
        for b in words:
            if allowed is not None and min(i,j,K-1-i,K-1-j)>=4 and b not in allowed:continue
            if any(min(2+3*(i+h),2+3*(j+l),n-3-3*(i+h),n-3-3*(j+l))>=14 and m&16 and m&(40 if axis==1 else 130)
                   for (h,l),m in zip(product(range(2),repeat=2),b)):continue
            a,c,d,e=b;cost=3-a.bit_count()
            if i==K-1:cost+=3-d.bit_count()
            if j==K-1:cost+=3-c.bit_count()
            if i==j==K-1:cost+=3-e.bit_count()
            ls=[]
            if j>0:ls.append(((0,u,seam(j-1,K-1),a,d),-1))
            if j<K-1:ls.append(((0,u,seam(j,K-1),c,e),1))
            if i>0:ls.append(((1,v,seam(i-1,K-1),a,c),-1))
            if i<K-1:ls.append(((1,v,seam(i,K-1),d,e),1))
            for z,_ in ls:eqs.setdefault(z,len(eqs))
            atoms.append((p,ls,cost))
    if '--parity' in sys.argv:
        from .tile_family_parity import check
        check(atoms,eqs,sorted(B),integral_counts)
        return
    # Form the sparse constraint matrix by columns, including exact
    # normalization. A rational replay rounds residuals down by type.
    import numpy as np
    ps=sorted(B);idx={p:i for i,p in enumerate(ps)};num=len(ps)+len(eqs)
    h=hp.Highs();h.setOptionValue('output_flag',False);h.setOptionValue('threads',1)
    b=np.array(integral_counts(k)+[0]*len(eqs),dtype=float)
    h.addRows(num,b,b,0,[0]*(num+1),[],[])
    st=[0];indices=[];vs=[]
    for p,ls,c in atoms:
        dd=defaultdict(int)
        for z,s in ls:dd[len(ps)+eqs[z]]+=s
        indices.append(idx[p]);vs.append(1)
        for r,v in dd.items():
            if v:indices.append(r);vs.append(v)
        st.append(len(vs))
    size=len(atoms);h.addCols(size,[c for _,_,c in atoms],[0.]*size,[hp.kHighsInf]*size,len(indices),st,indices,vs)
    print('frame',w,'axis',axis,'templates',len(B),'variables',size,'rows',num,flush=True)
    for train in (39,81,221):
        rhs=integral_counts(train);h.changeRowsBounds(len(ps),np.arange(len(ps),dtype=np.int32),rhs,rhs)
        for sign in (1,-1):
            if sign==1:h.setMinimize()
            else:h.setMaximize()
            h.run();status=h.getModelStatus()
            if status!=hp.HighsModelStatus.kOptimal:print('LP status',status,flush=True);continue
            price=[Fraction(round(sign*z*100000),100000) for z in h.getSolution().row_dual]
            # Make every dual column valid exactly, even after recovery.
            adj=defaultdict(Fraction)
            for p,ls,c in atoms:
                slack=sign*c-price[idx[p]]-sum(s*price[len(ps)+eqs[z]] for z,s in ls)
                adj[p]=min(adj[p],slack)
            def val(kk):return sign*sum(m*(price[idx[p]]+adj[p]) for p,m in zip(ps,integral_counts(kk)))
            arr=[val(39+14*t) for t in range(3)]
            print(('lower' if sign==1 else 'upper'),'deficit training k',train,'Newton',
                  (arr[0],arr[1]-arr[0],arr[2]-2*arr[1]+arr[0]),'at train',val(train),'target',5*train-1+(train-5)//7,flush=True)
if __name__=='__main__':solve(*(int(v) for v in sys.argv[1:] if not v.startswith('--')))
