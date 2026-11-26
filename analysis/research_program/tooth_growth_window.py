"""Joint old/new corner test after erasing the NW tooth in a tight three-layer frame."""
from itertools import product,combinations
from pathlib import Path
import sys,subprocess
from .defect_window import table,window,DIR
from .tight_corner_sat import cover
from .free_growth_charge import test as grow
from .slit_star_transfer import frame_path

def test(n,d,a,b,R,sec):
    from pysat.formula import IDPool
    from pysat.pb import PBEnc
    tab=table(n);N=n+3;big=table(N);T,P,S=big
    V,parent,pc,sc,cap=grow(n,a,b,d,big,recover=True)
    marks,path=frame_path(n,0);old=set(product(range(R),repeat=2));star=(2,d)
    want=all((2+x,d+y) in old for x,y in ((0,0),*DIR))
    def emit(f,bit,flags,arc,sheet):
        for u,v in marks.items():
            if u in old:f.append([bit(*u)*(1 if v else -1)])
        vp=IDPool(start_from=f.nv+1);W={}
        def costs(q,mu,vs,guard):
            def forbidden(bad,extra):
                for mask,m in cover(bad):
                    f.append(guard+extra+[(-x if m>>h&1 else x) for h,x in enumerate(vs) if mask>>h&1])
            forbidden(tuple(z>mu+cap or z<mu for z in q),[])
            prev=0
            for v in sorted({z-mu for z in q if mu<z<=mu+cap}):
                y=vp.id();W[y]=v-prev;prev=v;forbidden(tuple(z>=mu+v for z in q),[y])
        dom=set(product(range(R+a),range(R+b)))
        def X(u):
            if u in V:return vp.id(('new',*u))
            return bit(u[0]-a,u[1]-b)
        def A(u,k):return vp.id(('dir',*u,k))
        for u in sorted(dom):
            i,j=u
            if u in V:
                f.append([X(u)*(1 if V[u] else -1)])
                # These known empty interior cells, except for the deleted
                # tooth itself, are also empty in the old square.
                if 2<=i-a<R and 2<=j-b<R and (i-a,j-b)!=(2,2):
                    f.append([bit(i-a,j-b)*(1 if V[u] else -1)])
            qs=[(i+x,j+y) for x,y in product(range(3),repeat=2)]
            if all(v in dom for v in qs):costs(P(T(1,i,j)),pc.get(u,0),[X(v) for v in qs],[])
            ds=tuple(k for k,(x,y) in enumerate(DIR) if 0<=i+x<N and 0<=j+y<N)
            ns=[(i+DIR[k][0],j+DIR[k][1]) for k in ds];ar=[A(u,k) for k in ds]
            if u in parent:
                for k,z in zip(ds,ar):f.append([z if parent[u]==k else -z])
            for z,y in combinations(ar,2):f.append([-z,-y])
            if all(v in dom for v in ns):
                for k in (-1,*ds):
                    costs(S(T(0,i,j),ds,k,k==-1,False),sc.get(u,0),[X(u),*[X(v) for v in ns]],ar if k<0 else [-A(u,k)])
            for k,v in zip(ds,ns):
                if k>=2 or v not in dom:continue
                y=A(u,k);z=A(v,k+2);f.extend([[-y,-z],[-X(u),y,z],[-X(v),y,z],[-y,X(u),X(v)],[-z,X(u),X(v)]])
        if W:f.extend(PBEnc.atmost(lits=list(W),weights=list(W.values()),bound=cap,top_id=vp.top).clauses)
        stem=Path(f'target/tooth_growth_{n}_{d}_{a}_{b}_{R}');fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
        f.to_file(str(fn))
        with stem.with_suffix('.log').open('w') as log:rc=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(fn),str(pr)],stdout=log).returncode
        if rc==20:
            out=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True,check=True).stdout
            assert b's VERIFIED' in out;stem.with_suffix('.check').write_bytes(out);print('UNSAT s VERIFIED',flush=True)
        else:print('joint regional SAT' if rc==10 else 'UNKNOWN',flush=True)
    window(n,'rim',1,tab,domain=old,want=want,defects={('s',*star)},orient=path,root_site=(n-1,n-1),emit_graph=emit)
if __name__=='__main__':test(*map(int,sys.argv[1:]))
