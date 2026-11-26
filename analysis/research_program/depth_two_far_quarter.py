"""Three filled quadrants: transpose west-star cases to the same north-star domain."""
from pathlib import Path
from hashlib import file_digest
from itertools import combinations,product
import subprocess,sys
from .defect_window import table,window,DIR
from .odd_frames import frame

def run(n,lo,hi,seconds,*,domain=None,distances=None,output=None,replay=None,root_site=None,extra=None,turn_domain=None,matching=False,extra_graph=None):
    assert n%42==35 and n>=119
    dep=lambda u:min(*u,n-1-u[0],n-1-u[1])
    nb=lambda u,d:(u[0]+DIR[d][0],u[1]+DIR[d][1])
    dom=domain if domain is not None else {u for u in product(range(n),repeat=2) if dep(u)<8 or u[0]<=n//2 or u[1]>=n//2}
    frames=[frame(n,(0,*w)) for w in product((1,3),repeat=3)]
    frames+= [{(j,i):b for (i,j),b in m.items()} for m in frames]
    root=root_site or (n-1,n-1);paths=[]
    for m in frames:
        path={root:-1};q=[root]
        for u in q:
            for d in range(4):
                v=nb(u,d)
                if dep(v)==0 and v not in path and (m[u] or m[v]):
                    path[v]=(d+2)%4;q.append(v)
        assert len(q)==4*n-4;paths.append(path)
    common={u:d for u,d in paths[0].items() if all(p[u]==d for p in paths)}
    sites={('s',2,d) for d in (distances if distances is not None else range(5,n-5,6)) if lo<=d<=hi}
    tables=table(n)
    def emit(f,bit,flags,arc,sheet):
        assert set(flags)==sites
        # At an artificial convex corner a fringe vertex need not neighbor
        # any complete star. Preallocate even its previously unused arc
        # and sheet IDs before allocating selectors outside the ID pool.
        top=f.nv
        for u in sorted(dom):
            ds=[d for d in range(4) if nb(u,d) in dom]
            if all(d in ds or dep(nb(u,d))<0 for d in range(4)):continue
            top=max(top,bit(*u),sheet(*u))
            for d in ds:
                v=nb(u,d);top=max(top,arc(*u,d),arc(*v,(d+2)%4),sheet(*v))
                for e in range(4):
                    if nb(v,e) in dom and e!=(d+2)%4:top=max(top,arc(*v,e))
        for u in frames[0]:
            if u in dom:top=max(top,bit(*u))
        sels=list(range(top+1,top+17));f.append(sels)
        for u in sorted(frames[0]):
            if u not in dom:continue
            lits=[bit(*u)*(1 if m[u] else -1) for m in frames]
            if len(set(lits))==1:f.append([lits[0]])
            else:
                for sel,z in zip(sels,lits):f.append([-sel,z])
        for u in paths[0].keys()-common.keys():
            if u not in dom:continue
            for d in range(4):
                if nb(u,d) not in dom:continue
                for sel,p in zip(sels,paths):f.append([-sel,arc(*u,d)*(1 if p[u]==d else -1)])
        # The incomplete stars at the artificial fringe still inherit
        # direction consistency from the same actual rooted forest.
        for u in sorted(dom):
            ds=[d for d in range(4) if nb(u,d) in dom]
            if all(d in ds or dep(nb(u,d))<0 for d in range(4)):continue
            if u in common:
                for d in ds:f.append([arc(*u,d)*(1 if common[u]==d else -1)])
            for d,e in combinations(ds,2):f.append([-arc(*u,d),-arc(*u,e)])
            for d in ds:
                v=nb(u,d);a=arc(*u,d);b=arc(*v,(d+2)%4)
                f.extend([[-a,-b],[-bit(*u),a,b],[-bit(*v),a,b],[-a,bit(*u),bit(*v)],[-b,bit(*u),bit(*v)]])
                for e in range(4):
                    if nb(v,e) not in dom or e==(d+2)%4:continue
                    g=[-a,-arc(*v,e)];h=sheet(*u);k=sheet(*v)*(-1 if abs(d-e)==3 else 1)
                    f.extend([g+[-h,k],g+[h,-k]])
        if extra:extra(f,bit,flags)
        if extra_graph:extra_graph(f,bit,flags,arc,sheet)
        stem=Path(output or f'target/depth_two_far_quarter_{n}_{lo}_{hi}');cnf=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
        log=stem.with_suffix('.log')
        if seconds==-2:
            from tempfile import TemporaryFile
            with TemporaryFile(mode='w+',dir='target') as tmp:
                f.to_fp(tmp);tmp.flush();tmp.seek(0)
                new=file_digest(tmp.buffer,'sha256').hexdigest()
            with cnf.open('rb') as src:old=file_digest(src,'sha256').hexdigest()
            print('selector allocation audit: formula identical',new==old,'new',new,'previous',old,flush=True)
            return new==old
        if seconds:
            f.to_file(str(cnf));f.clauses.clear()
            with cnf.open('rb') as src:print('region',len(dom),'frames including reflection',len(frames),'distances',len(sites),'common perimeter directions',len(common),'sha256',file_digest(src,'sha256').hexdigest(),flush=True)
            if seconds==-3:return
            with log.open('w') as out:st=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(cnf),str(pr)],stdout=out).returncode
        else:st=10
        if st==20:
            with stem.with_suffix('.check').open('wb') as out:subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(pr)],stdout=out,check=True)
            assert b's VERIFIED' in stem.with_suffix('.check').read_bytes()
            print('both arms all eight frames s VERIFIED',flush=True)
        elif st==10:
            model={int(z) for s in log.read_text().splitlines() if s.startswith('v ') for z in s[2:].split()}
            if replay and len(model)-1<f.nv:
                # Some competition logs omit literals. Never interpret an
                # absent mark or selector as false without completing it.
                from pysat.solvers import Solver
                with Solver(name='cadical195') as sol,cnf.open() as src:
                    for line in src:
                        if line.startswith('p'):continue
                        cl=[int(z) for z in line.split()[:-1]]
                        if not any(z in model for z in cl):sol.add_clause([z for z in cl if -z not in model])
                    assert sol.solve(),'logged partial assignment does not extend'
                    model.update(z for z in sol.get_model() if -z not in model)
            site,=[u for u,v in flags.items() if v in model];w=next(k for k,z in enumerate(sels) if z in model)
            X={u for u in dom if bit(*u) in model}
            assert all((u in X)==bool(b) for u,b in frames[w].items() if u in dom)
            par={}
            def rt(u):
                while u in par:u=par[u]
                return u
            forest=dom if turn_domain is None else turn_domain
            for u in forest:
                for d in (0,1):
                    v=nb(u,d)
                    if v in forest and (u in X or v in X):
                        a,b=rt(u),rt(v);assert a!=b;par[a]=b
            print('partial forest only; frame index',w,'charged site',site,flush=True)
            if replay:
                out={}
                for u in dom:
                    dirs=[d for d in range(4) if nb(u,d) in dom and arc(*u,d) in model]
                    assert len(dirs)<=1
                    if dirs:out[u]=dirs[0]
                replay(w,site[1:],X,out)
        else:print('UNKNOWN')
    window(n,'rim',8,tables,domain=dom,root_site=root,orient=common,defects=sites,emit_graph=emit,turn_domain=turn_domain,matching=matching,outward_completion=matching)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
