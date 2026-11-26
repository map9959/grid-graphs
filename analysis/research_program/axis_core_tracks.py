"""Transfer the verified two-gap core's local constraints to one-gap rootings."""
from collections import Counter
from functools import lru_cache
from hashlib import file_digest
from itertools import combinations,product
from pathlib import Path
import inspect,subprocess,sys
from .defect_window import table,window,DIR
from .square_dual_physical import trans
from .slit_star_transfer import frame_path

def run(lo,hi,seconds):
    from pysat.formula import CNF,IDPool
    n=245;tab=table(n)
    stem=Path('target/two_gap_245_all_axis')
    data=[tuple(map(int,l.split()[:-1])) for l in stem.with_suffix('.core').read_text().splitlines() if l and not l.startswith(('p','c'))]
    def emit(original,bit,flags):
        base=original.nv;assert base==838361
        pool=inspect.getclosurevars(bit).nonlocals['vp'];source={abs(z):pool.obj(abs(z)) for c in data for z in c}
        original.clauses.clear()
        inds=list(range(14,n-14,3));first=base+16
        for z in source:
            if z==first:source[z]=('axis',)
            if first<z<=first+len(inds):source[z]=('row',inds[z-first-1])
            if first+len(inds)<z<=first+2*len(inds):source[z]=('col',inds[z-first-1-len(inds)])
        # Neither frame selection nor the cardinality of the two-gap
        # exit transfers. Retain only physical and validated axis clauses.
        keep=[c for c in data if all(source[abs(z)] is not None for z in c)]
        assert all(source[abs(z)][0] in ('v','a','ext','face','turn','axis','row','col') for c in keep for z in c)
        out=CNF();vp=IDPool();key=vp.id
        sites={(2,d):key(('star',d)) for d in range(lo,hi+1,6)}
        out.append(list(sites.values()))
        out.extend([[-u,-v] for u,v in combinations(sites.values(),2)])
        for (i,j),s in sites.items():
            for a,b in ((0,0),*DIR):out.append([-s,-key(('v',i+a,j+b))])
        records=[frame_path(n,w) for w in range(16)]
        selectors=[key(('frame',w)) for w in range(16)];out.append(selectors)
        for u in sorted(records[0][0]):
            vs=[key(('v',*u))*(1 if rec[0][u] else -1) for rec in records]
            if len(set(vs))==1:out.append([vs[0]])
            else:out.extend([[-s,v] for s,v in zip(selectors,vs)])
        guarded=Counter()
        for g in range(8):
            pos=lambda i,j:trans(i,j,n,g)
            ds=[DIR.index(tuple(b-a for a,b in zip(pos(30,30),pos(30+di,30+dj)))) for di,dj in DIR]
            @lru_cache(None)
            def mapped(z):
                tag,*args=source[z]
                if tag in ('v','a'):
                    u=pos(*args[:2])
                    if tag=='v':return key(('v',*u))
                    d=ds[args[2]];v=u[0]+DIR[d][0],u[1]+DIR[d][1]
                    per=lambda p:min(*p,n-1-p[0],n-1-p[1])==0
                    # Only perimeter-path edges can reverse on rerooting.
                    return key(('a',*u,d,g if per(u) and per(v) else -1))
                return key(('private',g,z))
            for c in keep:
                extra=[]
                if len(c)>=4 and all(z>0 for z in c):
                    arcs=[source[z] for z in c if source[z][0]=='a']
                    if len(arcs)==4 and len({q[1:3] for q in arcs})==1 and {q[3] for q in arcs}==set(range(4)):
                        u=pos(*arcs[0][1:3])
                        if u in sites:
                            # The no-outgoing, zero-charge star pattern is
                            # the only source rule the charged isolate may
                            # violate. Guards for other outchoices are false.
                            extra=[sites[u]];guarded[g]+=1
                out.append(extra+[mapped(abs(z))*(1 if z>0 else -1) for z in c])
            root=pos(0,0)
            for w,(marks,_) in enumerate(records):
                path={root:-1};todo=[root]
                for u in todo:
                    for d,(a,b) in enumerate(DIR):
                        v=u[0]+a,u[1]+b
                        if v in path or v not in marks or min(*v,n-1-v[0],n-1-v[1])!=0:continue
                        if marks[u] or marks[v]:path[v]=(d+2)%4;todo.append(v)
                assert len(path)==4*n-4
                for u,p in path.items():
                    for d,(a,b) in enumerate(DIR):
                        v=u[0]+a,u[1]+b
                        if v not in path:continue
                        out.append([-selectors[w],key(('a',*u,d,g))*(1 if d==p else -1)])
        st=Path(f'target/axis_core_tracks_{lo}_{hi}');fn=st.with_suffix('.cnf');pr=st.with_suffix('.drat')
        out.to_file(str(fn));out.clauses.clear()
        with fn.open('rb') as fd:print('core clauses per image',len(keep),'relaxed isolate guards',dict(guarded),'sha256',file_digest(fd,'sha256').hexdigest(),flush=True)
        with st.with_suffix('.log').open('w') as fd:r=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(fn),str(pr)],stdout=fd).returncode
        if r==20:
            proof=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True,check=True).stdout
            assert b's VERIFIED' in proof;st.with_suffix('.check').write_bytes(proof);print('s VERIFIED all 16 frame words')
        elif r==10:
            model={int(z) for line in st.with_suffix('.log').read_text().splitlines() if line.startswith('v ') for z in line[2:].split()}
            print('core relaxation SAT, selected star',[u for u,v in sites.items() if v in model])
        else:print('UNKNOWN')
    window(n,'rim',n,tab,matching=True,exit_only=True,emit=emit)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
