"""Test a common one-gap star defect with the whole grounded perimeter present."""
from itertools import product,combinations
from pathlib import Path
import subprocess,sys
from pysat.solvers import Solver
from .defect_window import table,window,DIR
from .odd_frames import frame

def run(n,H):
    T=table(n);typ,patch,star=T
    depth=lambda u:min(*u,n-1-u[0],n-1-u[1])
    rim={u for u in product(range(n),repeat=2) if depth(u)<H}
    Lstar='--star-L' in sys.argv
    if Lstar:rim={u for u in rim if min(u)<H}
    omit=next((s.split('=')[1] for s in sys.argv if s.startswith('--patch-omit=')),None)
    if omit:
        assert omit in ('NW','NE','SW','SE')
        rim.update((i,j) for i,j in product(range(n),repeat=2) if
                   i==n//2 or j==n//2 or ('N' if i<n//2 else 'S')+('W' if j<n//2 else 'E')!=omit)
    patch_band=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--patch-band=')),None)
    optional='--outside-ok' in sys.argv
    if patch_band:
        assert omit and '--any-patch' in sys.argv
        rim={u for u in rim if min(u)<patch_band}
    if optional:assert omit and '--any-patch' in sys.argv
    quad=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--nw=')),0)
    if quad:
        assert H<quad<=n//2+1
        rim.update(product(range(quad),repeat=2))
    local='--corner-only' in sys.argv
    half=next((z.split('=')[1] for z in sys.argv if z.startswith('--half=')),None)
    third=next((z.split('=')[1] for z in sys.argv if z.startswith('--third=')),None)
    if third:assert half and third in ('near','far')
    if half:
        assert not quad and not local and half in ('north','west')
        halfside=0 if half=='north' else 1
        rim.update(u for u in product(range(n),repeat=2) if u[halfside]<=n//2)
        if third:
            rim.update(u for u in product(range(n),repeat=2) if
                       (u[1-halfside] if third=='near' else n-1-u[1-halfside])<=n//2)
        band=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--band=')),None)
        if band:
            assert third=='far' and H<=band<=n//2+1
            rim={u for u in rim if depth(u)<H or u[halfside]<band or n-1-u[1-halfside]<band}
            third+=f'_band{band}'
        seam=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--seam=')),None)
        if seam is not None:
            assert third=='far' and seam%3==0 and 12<=seam<n-53
            # Leave only the straight H-row rim in each replaceable corridor.
            rim={u for u in rim if depth(u)<H or all(not seam-2<=a<=seam+40 for a in u)}
            third+=f'_seam{seam}'
        if '--se-only' in sys.argv:
            assert third=='far'
            rim={u for u in rim if depth(u)<H or min(u)>=n-60}
            third='far_SE60'
        if third:print('joint domain',half,'third',third,'vertices',len(rim),flush=True)
    if local:
        assert quad
        # Include a halo even at the last tested longitudinal site.
        rim=set(product(range(quad+2),repeat=2))
    roots=((0,0),(0,n-1),(n-1,n-1),(n-1,0))
    words=[(0,*w) for w in product((1,3),repeat=3)]
    if local:words=[(0,1,1,1)]
    frames=[frame(n,w) for w in words]
    def nb(u,d):return tuple(x+y for x,y in zip(u,DIR[d]))
    def parents(m,root):
        q=[root];p={root:-1}
        for u in q:
            for d in range(4):
                v=nb(u,d)
                if depth(v)==0 and v not in p and (m[u] or m[v]):
                    p[v]=(d+2)%4;q.append(v)
        assert len(q)==4*n-4
        return p
    paths=[parents(frames[0],r) for r in roots]
    for m in frames:assert parents(m,roots[0])==paths[0]
    def emit(f,bit,flags,arc,sheet):
        if '--patch-core' in sys.argv:
            p=Path(f'target/star_rim_{n}_{H}_0_0_rim_base_patch_omit_{omit}_any.core')
            used={abs(int(z)) for line in p.open() if not line.startswith('p') for z in line.split()}
            pts=[u for u in rim if bit(*u) in used]
            from collections import Counter
            print(omit,'physical mark sites',len(pts),'depths',sorted(Counter(map(depth,pts)).items()),
                  'bounds',[(min(u[k] for u in pts),max(u[k] for u in pts)) for k in range(2)],flush=True)
            print('tiles',sorted(Counter((i//15,j//15) for i,j in pts).items()))
            return
        if '--core-map' in sys.argv:
            from .star_core_transfer import extract
            return extract(n,H,half,rim,bit,arc,sheet)
        ds={u:[d for d in range(4) if nb(u,d) in rim] for u in rim}
        edges=[(u,nb(u,d),d) for u in sorted(rim) for d in ds[u] if d<2]
        for u in sorted(rim):
            if u in paths[0]:
                for d in ds[u]:f.append([arc(*u,d) if d==paths[0][u] else -arc(*u,d)])
            for d,e in combinations(ds[u],2):f.append([-arc(*u,d),-arc(*u,e)])
            for d in ds[u]:
                v=nb(u,d);a=arc(*u,d);b=arc(*v,(d+2)%4)
                if d<2:f.extend([[-a,-b],[-bit(*u),a,b],[-bit(*v),a,b],[-a,bit(*u),bit(*v)],[-b,bit(*u),bit(*v)]])
                for e in ds[v]:
                    if e==(d+2)%4:continue
                    t=sheet(*v)*(-1 if abs(d-e)==3 else 1)
                    f.extend([[-a,-arc(*v,e),-sheet(*u),t],[-a,-arc(*v,e),sheet(*u),-t]])
        cand={}
        if omit:
            from .common_patch import candidates
            origins=set(candidates(n))
        for (kind,i,j),z in flags.items():
            if omit and kind=='p' and '--any-patch' in sys.argv:
                cand[i,j]=z
            elif omit and kind=='p' and (i,j) in origins and (i+j)%2:
                cand[i,j]=z
                corners=[bit(i+a,j+b) for a,b in product((0,2),repeat=2)]
                f.append([-z,*corners])
                for a,b in combinations(corners,2):f.append([-z,-a,-b])
                for a,b in product(range(3),repeat=2):
                    if a==1 or b==1:f.append([-z,-bit(i+a,j+b)])
                for ri,cj in ((0,1),(1,0),(1,1)):
                    y=n-3-i if ri else i;x=n-3-j if cj else j
                    if max(y,x)>22:continue
                    maskids=[2*ri+cj]
                    if (y,x) in ((4,7),(4,13)):maskids.append(2*ri+1-cj)
                    if (y,x) in ((7,4),(13,4)):maskids.append(2*(1-ri)+cj)
                    for k in maskids:f.append([-z,-corners[k]])
            elif not omit and kind=='s' and depth((i,j))==2 and (i+j)%3==1:cand[i,j]=z
            else:f.append([-z])
        selectors=[]
        for m in frames:
            z=f.nv+1;selectors.append(z)
            for u,k in m.items():
                if u in rim:f.append([-z,bit(*u) if k else -bit(*u)])
        f.append(selectors)
        if half:
            phase=[z for u,z in cand.items() if u[halfside]==2 and u[1-halfside]%6==5
                   and 5<=u[1-halfside]<=n-6]
            assert len(phase)==len(range(5,n-5,6))
            f.append(phase)
        def replay(model):
            X={u for u in rim if bit(*u) in model};paid_sites=[u for u,z in cand.items() if z in model]
            if optional and not paid_sites:site=None
            else:site,=paid_sites
            out={};par={}
            def rt(u):
                while u in par:u=par[u]
                return u
            for u,v,d in edges:
                a,b=arc(*u,d) in model,arc(*v,(d+2)%4) in model
                assert a+b==int(u in X or v in X)
                if a or b:
                    x,y=rt(u),rt(v);assert x!=y;par[x]=y
                    src,k=(u,d) if a else (v,(d+2)%4)
                    assert src not in out;out[src]=k
            for i,j in rim:
                sq=[(i+a,j+b) for a,b in product(range(3),repeat=2)]
                if all(v in rim for v in sq):
                    mask=sum((v in X)<<k for k,v in enumerate(sq))
                    paid=bool(omit and (i,j)==site)
                    assert patch(typ(1,i,j))[mask]==72*paid
                    if paid and '--any-patch' not in sys.argv:assert mask in (1,4,64,256)
            for root,p in zip(roots,paths):
                o={**out,**p}
                for u,v,d in edges:assert int(o.get(u)==d)+int(o.get(v)==(d+2)%4)==int(u in X or v in X)
                for u in rim:
                    dirs=tuple(ds[u])
                    if any(d not in dirs and depth(nb(u,d))>=0 for d in range(4)):continue
                    m=int(u in X)+sum((nb(u,d) in X)<<(k+1) for k,d in enumerate(dirs))
                    assert star(typ(0,*u),dirs,o.get(u,-1),u==root,len(dirs)==2)[m]==72*bool(not omit and u==site)
            return site
        def prove(units,label):
            path=Path(f'target/star_rim_{n}_{H}_{quad}_{int(local)}_{half or "rim"}_{third or "base"}_{label}.cnf');proof=path.with_suffix('.drat')
            fixed=f.copy();fixed.extend(units);fixed.to_file(str(path))
            assert subprocess.run(['target/cadical/build/cadical',str(path),str(proof)],capture_output=True).returncode==20
            r=subprocess.run(['target/drat-trim/drat-trim',str(path),str(proof)],capture_output=True)
            assert r.returncode==0 and b's VERIFIED' in r.stdout
            print(label,'s VERIFIED',flush=True)
        with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
            if Lstar:
                assert H==7 and not optional and not half and not omit
                for w,z in zip(words,selectors):
                    yes=[[],[]];bad=[]
                    for arm in (0,1):
                        for ell in range(5,n-5,3):
                            u=(2,ell) if arm==0 else (ell,2)
                            k=cand[u]
                            if not s.solve(assumptions=[z,k]):bad.append(k);continue
                            model=set(s.get_model());assert replay(model)==u
                            assert all((bit(*v) in model)==bool(b) for v,b in frame(n,w).items() if v in rim)
                            yes[arm].append(ell)
                    if bad:prove([[z],bad],'starL_'+''.join(map(str,w)))
                    print(w,'N/W replayed',list(map(len,yes)),'excluded distances',
                          [sorted(set(range(5,n-5,3))-set(q)) for q in yes],flush=True)
                return
            if omit:
                bad=[]
                for w,z in zip(words,selectors):
                    if not s.solve(assumptions=[z]):bad.append(z);continue
                    model=set(s.get_model());site=replay(model)
                    assert all((bit(*u) in model)==bool(k) for u,k in frame(n,w).items() if u in rim)
                    if site is None:print(w,'zero visible charge replayed',flush=True);continue
                    i,j=site
                    mask=sum((bit(i+a,j+b) in model)<<(3*a+b) for a,b in product(range(3),repeat=2))
                    print(w,'origin',(i,j),'mask',mask,'replayed',flush=True)
                if bad:prove([bad],'patch_omit_'+omit+('_any' if '--any-patch' in sys.argv else '')+(f'_b{patch_band}' if patch_band else '')+('_optional' if optional else ''))
                print('omit',omit,'origins',len(cand),'excluded frames',len(bad),'of',len(words),flush=True)
                return
            if half:
                if '--each-site' in sys.argv:
                    missing=[]
                    for w,z in zip(words,selectors):
                        hits=[];bad=[]
                        for u,k in sorted(cand.items()):
                            if k not in phase:continue
                            if s.solve(assumptions=[z,k]):
                                model=set(s.get_model())
                                assert replay(model)==u and all((bit(*v) in model)==bool(b) for v,b in frame(n,w).items())
                                hits.append(u[1-halfside])
                            else:bad.append(k)
                        if bad:missing.append((z,bad))
                        print(w,'replayed distances',hits,flush=True)
                    if missing:
                        ids=list(range(f.nv+1,f.nv+1+len(missing)))
                        for a,(z,bad) in zip(ids,missing):f.append([-a,z]);f.append([-a,*bad])
                        prove([ids],half+'_sites')
                    print('frame/location pairs checked',len(words)*len(phase),'excluded',sum(len(b) for _,b in missing),flush=True)
                    return
                bad=[]
                for w,z in zip(words,selectors):
                    if s.solve(assumptions=[z]):
                        model=set(s.get_model());site=replay(model)
                        assert cand[site] in phase and all((bit(*u) in model)==bool(k) for u,k in frame(n,w).items())
                        print(w,'replayed',site,flush=True)
                    else:bad.append(z)
                if bad:prove([bad],half)
                print(n,half,'vertices',len(rim),'eligible locations',len(phase),'excluded frames',len(bad),'of',len(words),flush=True)
                return
            if not s.solve():prove([],'all');return
            groups={}
            for (i,j),x in cand.items():
                side=(i,n-1-j,n-1-i,j).index(2)
                coord=(j,i,n-1-j,n-1-i)[side]
                if min(coord,n-1-coord)<5:continue
                if quad and side not in (0,3):continue
                if local and max(i,j)>=quad:continue
                key=(side,coord%6)
                if quad:key+=(max(i,j)<quad,)
                if '--zones' in sys.argv:
                    key+=(coord if coord<12 else coord-n+1 if coord>=n-12 else 'middle',)
                groups.setdefault(key,[]).append(x)
            # One selector queries a whole clockwise side/phase class.
            gs={}
            for k,xs in sorted(groups.items(),key=lambda item:str(item[0])):
                g=f.nv+1;gs[k]=g;f.append([-g]+xs);s.add_clause([-g]+xs)
            for w,z in zip(words,selectors):
                good=[];bad=[]
                for k,g in gs.items():
                    if s.solve(assumptions=[z,g]):
                        site=replay(set(s.get_model()));assert cand[site] in groups[k];good.append(k)
                    else:bad.append(k)
                if bad:prove([[z],[gs[k] for k in bad]],''.join(map(str,w)))
                print(w,'four-root side/phase',good,'excluded',bad,flush=True)
    window(n,'rim',H,T,orient=paths[0],domain=rim,emit_graph=emit,free_defect=optional)
if __name__=='__main__':run(*map(int,sys.argv[1:3]))
