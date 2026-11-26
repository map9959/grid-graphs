"""All candidate stars lie north of this full-width southern rectangle."""
from itertools import product
from hashlib import file_digest
from pathlib import Path
import subprocess,sys
from .southwest_ports import patterns
from .defect_window import window,table,DIR
from .slit_star_transfer import frame_path

def run(a,b,seconds):
    n=245;A=set(product(range(100,n),range(n)));X=patterns()
    fp=[frame_path(n,w) for w in range(16)]
    frames={tuple(sorted((u,v) for u,v in m.items() if u in A)) for m,p in fp}
    core={u for u in A if u[0]>=101}
    archive=Path(__file__).with_name('one_gap_projection_examples')/f'south_245_{a}_{b}.gz'
    def replay(word,marks,out):
        from .shorten_245_star import audit,nb
        hits=[s for s in range(a,b+1) if all((u in marks)==bool(x) for u,x in X[s].items())];assert hits
        assert all(u in marks or any(nb(u,k) in marks for k in range(4))
                   for u in product(range(102,237),range(8,143)))
        v,e,cc=audit(n,core,marks,out,None,None,tab,fp[word],(244,244))
        print('southern forest, sites',v,'forced edges',e,'components',len(set(cc.values())),'cycle rank 0; zero charges; starts',hits)
    tab=table(n)
    if seconds==-1:
        import gzip
        raw=gzip.decompress(archive.read_bytes());data=dict(zip(sorted(core),raw[1:],strict=True))
        replay(raw[0],{u for u,v in data.items() if v>=5},{u:v%5-1 for u,v in data.items() if v%5})
        return
    orient={u:d for u,d in fp[0][1].items() if u in A}
    assert all(all(p[u]==d for u,d in orient.items()) for m,p in fp)
    stem=Path(f'target/sw_strip_{a}_{b}');fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
    def emit(f,bit,flags,arc,sheet):
        top=f.nv;sels=list(range(top+1,top+1+len(frames)));f.append(sels)
        words=[dict(m) for m in sorted(frames)]
        for u in sorted(words[0]):
            ls=[bit(*u)*(1 if m[u] else -1) for m in words]
            if len(set(ls))==1:f.append([ls[0]])
            else:
                for z,v in zip(sels,ls):f.append([-z,v])
        ss=list(range(f.nv+1,f.nv+2+b-a));f.append(ss)
        for s,z in zip(range(a,b+1),ss):
            for u,v in X[s].items():f.append([-z,bit(*u) if v else -bit(*u)])
        for i,j in product(range(102,237),range(8,143)):
            f.append([bit(i,j),*(bit(i+x,j+y) for x,y in DIR)])
        if seconds:f.to_file(str(fn))
        f.clauses.clear()
        with fn.open('rb') as fd:print('south region',len(A),'frame restrictions',len(frames),'all 512 frame/site cases','start range',a,b,'sha256',file_digest(fd,'sha256').hexdigest(),flush=True)
        log=stem.with_suffix('.log')
        if seconds:
            with log.open('w') as fd:st=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(fn),str(pr)],stdout=fd).returncode
        else:st=10
        if st==20:
            with stem.with_suffix('.check').open('wb') as fd:subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],stdout=fd,check=True)
            assert b's VERIFIED' in stem.with_suffix('.check').read_bytes()
            print('UNSAT s VERIFIED',a,b)
        elif st==10:
            from .shorten_245_star import audit,nb
            from pysat.solvers import Solver
            model={int(z) for l in log.read_text().splitlines() if l.startswith('v ') for z in l[2:].split()}
            if len(model)-1<f.nv:
                with Solver(name='cadical195') as sol,fn.open() as src:
                    for line in src:
                        if line.startswith('p'):continue
                        cl=list(map(int,line.split()[:-1]))
                        if not any(z in model for z in cl):sol.add_clause([z for z in cl if -z not in model])
                    assert sol.solve()
                    model.update(z for z in sol.get_model() if -z not in model)
            # Removing the artificial first row keeps the entire southwest.
            marks={u for u in core if bit(*u) in model};out={}
            for u in core:
                directions=[d for d in range(4) if nb(u,d) in core and arc(*u,d) in model]
                assert len(directions)<=1
                if directions:out[u]=directions[0]
            word=next(k for k,(m,p) in enumerate(fp) if all((u in marks)==bool(x) for u,x in m.items() if u in core))
            replay(word,marks,out)
            import gzip
            if not archive.exists():archive.write_bytes(gzip.compress(bytes([word])+bytes(5*int(u in marks)+1+out.get(u,-1) for u in sorted(core)),mtime=0))
        else:print('UNKNOWN')
    window(n,'rim',1,tab,domain=A,want=False,orient=orient,root_site=(244,244),emit_graph=emit)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
