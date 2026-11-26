"""Mask-conditioned zero-charge extensions near two sides, one side, or neither."""
from itertools import product
from pathlib import Path
import subprocess
from pysat.solvers import Solver
from .defect_window import window,table,DIR
from .odd_frames import frame

def run():
    n=119;tables=table(n);typ,patch,star=tables
    # A window in coordinates measured from the nearest corner: fixed
    # axis if <=22, else shift one of 61,64 by a multiple of six.
    # Verify the clipped near/far coordinates in both orientations.
    def ax(x,S,h):return x if x<h else 2*h+3+x-S if x>=S-h else h+(x-h)%3
    for N in (119,161):
        for origin in range(4,(N-3)//2+1,3):
            near=origin<=22;ref=origin if near else 61+(origin-61)%6
            lo,hi=(0,41) if near else (45,83)
            for tag in (0,1):
                S=N-2*tag;s=n-2*tag;h=6-tag
                for x in range(lo,hi-2*tag):
                    y=x+origin-ref
                    assert 0<=y<S
                    assert (ax(x,s,h),ax(s-1-x,s,h))==(ax(y,S,h),ax(S-1-y,S,h))
        print('window charges invariant on side',N,flush=True)
    for near1,near2 in ((1,1),(1,0),(0,0)):
        def axis(near):return (range(41),range(4,23,3)) if near else (range(45,83),(61,64))
        ii,ys=axis(near1);jj,xs=axis(near2);domain=set(product(ii,jj))
        for w in (range(4) if near1 and near2 else (0,)):
            marks=frame(n,(w,0 if w in (1,3) else 1,1,1))
            parent={(0,0):-1};q=[(0,0)]
            for i,j in q:
                for d,(a,b) in enumerate(DIR):
                    u=i+a,j+b
                    if u in marks and min(*u,n-1-u[0],n-1-u[1])==0 and u not in parent and (marks[i,j] or marks[u]):
                        q.append(u);parent[u]=(d+2)%4
            def emit(f,bit,flags,arc,sheet):
                for u in domain & marks.keys():f.append([bit(*u) if marks[u] else -bit(*u)])
                bad=[];good=[];by={}
                with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
                    for i,j in product(ys,xs):
                        if (i+j)%2==0:continue
                        box=[(i+a,j+b) for a,b in product(range(3),repeat=2)]
                        vs=[bit(*u) for u in box];keep=[]
                        for mask in (1,4,64,256):
                            units=[flags['p',i,j]]+[z if mask>>k&1 else -z for k,z in enumerate(vs)]
                            if not s.solve(assumptions=units):bad.append(units);continue
                            model=set(s.get_model());X={u for u in domain if bit(*u) in model}
                            assert sum((u in X)<<k for k,u in enumerate(box))==mask
                            # Independent physical replay of charges and forest
                            # on the window minus its artificial outer layer.
                            par={}
                            def root(u):
                                while u in par:u=par[u]
                                return u
                            for y,x in domain:
                                sq=[(y+a,x+b) for a,b in product(range(3),repeat=2)]
                                if all(u in domain for u in sq):
                                    h=sum((u in X)<<k for k,u in enumerate(sq))
                                    assert patch(typ(1,y,x))[h]==72*((y,x)==(i,j))
                                ds=tuple(d for d,(a,b) in enumerate(DIR) if 0<=y+a<n and 0<=x+b<n)
                                nb=[(y+DIR[d][0],x+DIR[d][1]) for d in ds]
                                if not all(u in domain for u in nb):continue
                                outs=[d for d in ds if arc(y,x,d) in model];assert len(outs)<=1
                                h=int((y,x) in X)+sum((u in X)<<(k+1) for k,u in enumerate(nb))
                                assert star(typ(0,y,x),ds,next(iter(outs),-1),(y,x)==(0,0),len(ds)==2)[h]==0
                                for d,u in zip(ds,nb):
                                    if d<2 and ((y,x) in X or u in X):
                                        A,B=root((y,x)),root(u);assert A!=B;par[A]=B
                            good.append((i,j,mask));keep.append(mask)
                        by[i,j]=keep
                if bad:
                    # One checked disjunction covers every negative decision.
                    sels=list(range(f.nv+1,f.nv+1+len(bad)));f.append(sels)
                    for z,units in zip(sels,bad):
                        for lit in units:f.append([-z,lit])
                    stem=Path(f'target/patch_nb_{near1}{near2}_{w}');cnf=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
                    f.to_file(str(cnf));assert subprocess.run(['target/cadical/build/cadical',str(cnf),str(pr)],capture_output=True).returncode==20
                    chk=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(pr)],capture_output=True)
                    assert chk.returncode==0 and b's VERIFIED' in chk.stdout
                print((near1,near2),w,'replayed',len(good),'checked exclusions',len(bad),by,flush=True)
            window(n,'rim',0,tables,matching=True,domain=domain,orient=parent,emit_graph=emit)
if __name__=='__main__':run()
