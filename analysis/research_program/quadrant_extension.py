"""Existential NW-quadrant extension of the same central-cross connector."""
from itertools import product,combinations
from pathlib import Path
import subprocess,sys
from pysat.solvers import Solver
from pysat.formula import CNF
from .defect_window import window,table,DIR
from .rim_connector import install,replay
from .interior_connector import CODES
from .odd_frames import frame

def run(n,cap=0,combined=False,seams=False,free_path=False,route='cross',anchor=None,band=None):
    assert n>=119 and (n-119)%42==0
    data=table(n);typ,patch,star=data;mid=n//2 if anchor is None else anchor
    cross={(i,j) for i,j in product(range(n),repeat=2) if
           min(i,j,n-1-i,n-1-j)<7 or min(abs(i-mid),abs(j-mid))<=2}
    slots=range(mid+cap+1,mid+1) if cap<0 else range(cap or mid+1)
    if seams:
        # Leave two ordinary replaceable pieces in the NW half, one on
        # each axis. Their full neighborhoods must be unaltered.
        a=seams if type(seams)==int else 3*((mid//2-18)//3)
        assert a>=12 and a+36<mid-4
        slots=[v for v in slots if not a-2<=v<=a+37]
        print('replaceable longitudinal start',a,flush=True)
    added=set(product(slots,repeat=2))-cross
    if band is not None:
        added={u for u in added if min(u[0]-6,u[1]-6,mid-2-u[0],mid-2-u[1])<=band}
    domain=cross|added
    pts=sorted(domain);bits={u:k+1 for k,u in enumerate(pts)};nv=len(pts)
    def nb(u,d):return tuple(x+y for x,y in zip(u,DIR[d]))
    ds={u:[d for d in range(4) if nb(u,d) in domain] for u in pts}
    edges=[(u,nb(u,d),d) for u in pts for d in ds[u] if d<2]
    area=cross if route=='cross' else domain
    path_core=area if route=='domain' else {u for u in area if all((i,j) in area for i in range(max(0,u[0]-2),min(n,u[0]+3))
                                     for j in range(max(0,u[1]-2),min(n,u[1]+3)))}
    roots=[(0,0),(0,n-1),(n-1,n-1),(n-1,0)]
    frames={c:frame(n,tuple(map(int,c))) for c in CODES}
    prefix=Path(f'target/quad_{n}'+('' if route=='cross' else '_'+route)+
                ('' if anchor is None else f'_at{anchor}')+('' if band is None else f'_band{band}'));body=prefix.with_suffix('.body')
    views=[];rows=0
    with Solver(name='cadical195') as s, body.open('w') as stream:
        def put(c):
            nonlocal rows
            s.add_clause(c);stream.write(' '.join(map(str,c))+' 0\n');rows+=1
        def emit(f,bit,flags,arc,sheet):
            nonlocal nv
            av={(u,d):arc(*u,d) for u in pts for d in ds[u]}
            for u in pts:
                for d,e in combinations(ds[u],2):f.append([-av[u,d],-av[u,e]])
                for d in ds[u]:
                    v=nb(u,d);a=av[u,d];b=av[v,(d+2)%4]
                    if d<2:f.extend([[-a,-b],[-bit(*u),a,b],[-bit(*v),a,b],[-a,bit(*u),bit(*v)],[-b,bit(*u),bit(*v)]])
                    for e in ds[v]:
                        if e==(d+2)%4:continue
                        t=sheet(*v)*(-1 if abs(d-e)==3 else 1)
                        f.extend([[-a,-av[v,e],-sheet(*u),t],[-a,-av[v,e],sheet(*u),-t]])
            ids=list(range(nv,nv+f.nv+1));nv+=f.nv
            for u in pts:ids[bit(*u)]=bits[u]
            for c in f.clauses:put([ids[z] if z>0 else -ids[-z] for z in c])
            views.append({k:ids[z] for k,z in av.items()})
        for root in roots:window(n,'rim',7,data,exit_only=True,domain=domain,root_site=root,emit_graph=emit)
        f=CNF();f.nv=nv
        if free_path:
            sels={c:nv+i+1 for i,c in enumerate(frames)};f.nv=max(sels.values())
        else:sels,selected=install(f,lambda i,j:bits[i,j],[e for e in edges if e[0] in path_core and e[1] in path_core],n,frames)
        for c in f.clauses:put(c)
        stream.flush()
        print('side',n,'added quadrant sites',len(domain-cross),'clauses',rows,flush=True)
        for c,m in frames.items():
            for u,z in m.items():put([-sels[c],bits[u] if z else -bits[u]])
        stream.flush()
        if combined:put(list(sels.values()));stream.flush()
        for code in (['ALL'] if combined else frames):
            units=[] if combined else [sels[code]]
            if not s.solve(assumptions=units):
                import shutil
                fn=prefix.with_suffix('.cnf');pr=prefix.with_suffix('.drat')
                with fn.open('wb') as file,body.open('rb') as src:
                    file.write(f'p cnf {f.nv} {rows+len(units)}\n'.encode());shutil.copyfileobj(src,file)
                    for z in units:file.write(f'{z} 0\n'.encode())
                assert subprocess.run(['target/cadical/build/cadical',str(fn),str(pr)],capture_output=True).returncode==20
                res=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True)
                assert res.returncode==0 and b's VERIFIED' in res.stdout
                print(code,'UNSAT VERIFIED',flush=True);continue
            model=set(s.get_model());X={u for u,z in bits.items() if z in model}
            code=next(c for c,z in sels.items() if z in model);m=frames[code]
            par={u:u for u in pts}
            def rt(u):
                while par[u]!=u:u=par[u]
                return u
            for u,v,d in edges:
                if u in X or v in X:
                    a,b=rt(u),rt(v);assert a!=b;par[a]=b
            assert all((u in X)==bool(z) for u,z in m.items())
            for i,j in pts:
                box=[(i+a,j+b) for a,b in product(range(3),repeat=2)]
                if all(u in domain for u in box):assert patch(typ(1,i,j))[sum((u in X)<<k for k,u in enumerate(box))]==0
            arr=[]
            for root,av in zip(roots,views):
                out={u:d for (u,d),z in av.items() if z in model}
                assert len(out)==sum(z in model for z in av.values());paid=0
                for u,v,d in edges:assert int(out.get(u)==d)+int(out.get(v)==(d+2)%4)==int(u in X or v in X)
                for u in pts:
                    port=tuple(ds[u]);e=out.get(u,-1)
                    if any(all(0<=x<n for x in nb(u,d)) and d not in port for d in range(4)):continue
                    h=int(u in X)+sum((nb(u,d) in X)<<(k+1) for k,d in enumerate(port))
                    q=star(typ(0,*u),port,e,u==root,len(port)==2)[h]
                    if q:
                        assert q==72 and len(port)==3 and e in port
                        i,j=nb(u,e);assert min(i,j,n-1-i,n-1-j)==1;paid+=1
                assert paid==1;arr.append((root,out))
            result=None if free_path else replay(model,selected,m,n,arr)
            entered=set() if free_path else {u for edge,z in selected.items() if z in model for u in edge if u not in cross}
            print(code,'verified',result,'path sites in added square',len(entered),flush=True)
    body.unlink()
if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 0,'--all' in sys.argv,next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--seams=')),'--seams' in sys.argv),'--free-path' in sys.argv,'checked' if '--checked-route' in sys.argv else 'domain' if '--domain-route' in sys.argv else 'cross',*(next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--'+opt+'=')),None) for opt in ('anchor','band')))
