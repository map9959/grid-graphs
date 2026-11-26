"""NW triangle around both possible arms; test a phase class, not a fixed rim model."""
from .one_gap_rim import frame,DIR
from .defect_window import table,window
from pathlib import Path
from itertools import product
from hashlib import sha256
import subprocess,sys

def run(n,phase,limit,seconds,extra=0,closed=0,scan=0,start=5):
    assert n%42==35 and n>=119 and phase in (2,5)
    depths=[d for d in range(5,n-5,3) if d%6==phase and start<=d<=limit]
    defects={('s',i,j) for d in depths for i,j in ((2,d),(d,2))}
    # Three layers beyond the last depth; every candidate star complete.
    S={p for p in product(range(n),repeat=2) if
       (max(p)<=limit+2 if extra==-1 else sum(p)<=limit+5+extra)}
    if closed:
        assert extra==-1 and limit+2<n-6
        frames=[frame(n,(w,1,0,1)) for w in (1,3)]
    else:frames=[frame(n,(0,*w)) for w in product((1,3),repeat=3)]
    def parents(m):
        q=[(0,0)];path={q[0]:-1}
        for i,j in q:
            for d,(a,b) in enumerate(DIR):
                p=i+a,j+b
                if p in m and min(*p,n-1-p[0],n-1-p[1])==0 and p not in path and (m[p] or m[i,j]):
                    path[p]=(d+2)%4;q.append(p)
        assert len(path)==4*n-4
        return path
    path=parents(frames[0])
    assert all(parents(m)==path for m in frames)
    def emit(f,bit,flags):
        assert set(flags)==defects
        words={tuple(sorted((p,b) for p,b in m.items() if p in S)) for m in frames}
        sels=list(range(f.nv+1,f.nv+1+len(words)));f.append(sels)
        for a,word in zip(sels,sorted(words)):
            for p,b in word:f.append([-a,bit(*p) if b else -bit(*p)])
        stem=Path(f'target/depth_two_triangle_{n}_{phase}_{limit}'+(f'_plus{extra}' if extra else '')+('_closed' if closed else '')+(f'_from{start}' if start!=5 else ''));fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
        if scan:
            from pysat.solvers import Solver
            reject=[];good=[];unknown=[]
            with Solver(name='cadical195',bootstrap_with=f.clauses) as solver:
                for key,z in sorted(flags.items()):
                    # Reflection swaps the two closed frame words and arms.
                    solver.conf_budget(scan)
                    ok=solver.solve_limited(assumptions=[sels[0],z])
                    (good if ok is True else reject if ok is False else unknown).append(key[1:])
            print('restricted frame',sorted(words)[0][:3],'projected SAT',good,'UNKNOWN',unknown,'UNSAT',reject,flush=True)
            if not reject:return
            f.append([sels[0]]);f.append([flags['s',*p] for p in reject])
            stem=stem.with_name(stem.name+'_scan');fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
        if seconds:
            f.to_file(str(fn));f.clauses.clear()
            print('vertices',len(S),'distinct frame restrictions',len(words),'eligible sites',len(flags),'sha256',sha256(fn.read_bytes()).hexdigest(),flush=True)
            with stem.with_suffix('.log').open('w') as out:
                st=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(fn),str(pr)],stdout=out).returncode
        else:st=10
        if st==20:
            with stem.with_suffix('.check').open('wb') as out:
                subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],stdout=out,check=True)
            assert b's VERIFIED' in stem.with_suffix('.check').read_bytes()
            print('s VERIFIED:',reject if scan else ('both arms, distances',depths))
        elif st==10:
            model={int(z) for line in stem.with_suffix('.log').read_text().splitlines() if line.startswith('v ') for z in line[2:].split()}
            site,=[u[1:] for u,v in flags.items() if v in model]
            # Restrict to complete stars. All induced forced edges having
            # such an endpoint received the model's orientation constraints.
            X={u for u in S if bit(*u) in model}
            core={u for u in S if all((u[0]+a,u[1]+b) in S or not(0<=u[0]+a<n and 0<=u[1]+b<n) for a,b in DIR)}
            par={};cycles=0
            def rt(u):
                while u in par:u=par[u]
                return u
            for i,j in core:
                for a,b in DIR[:2]:
                    v=i+a,j+b
                    if v in core and ((i,j) in X or v in X):
                        x,y=rt((i,j)),rt(v)
                        if x==y:cycles+=1
                        else:par[x]=y
            assert not cycles and all((site[0]+a,site[1]+b) not in X for a,b in ((0,0),*DIR))
            print('SAT partial mark pattern; depth-two site',site,'checked complete-star core vertices',len(core),'forced cycles',cycles)
        else:print('UNKNOWN')
    window(n,'rim',1,table(n),domain=S,orient=path,emit=emit,defects=defects)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
