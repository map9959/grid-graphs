"""Price both cropped ends of one empty north band from the same score budget."""
from pathlib import Path
import subprocess,sys
from pysat.card import CardEnc
from .diagonal_score import generate

def test(n,lo,hi,cap,sec):
    assert n>=103 and (n-103)%9==0 and 2<=lo<=hi<=10
    k=n//3
    # Mirrored local 30-site crops; disjoint. Only complete atoms are
    # charged by generate(), with NW still the sole designated root.
    dom={(i,y) for i in range(30) for j in range(30)
         if i<=hi+4 or j<=11 for y in (j,n-1-j)}
    f,X=generate(n,3*k*k+(16*k-7)//3,dom)
    if '--reroot' in sys.argv:
        # Reflect the crop's physical marks only. Auxiliary variables,
        # including all arrow choices, get a separate root orientation.
        shift=f.nv
        shared={X[n*i+j]:X[n*i+n-1-j] for i,j in dom}
        for cl in f.clauses[:]:
            f.append([(1 if x>0 else -1)*shared.get(abs(x),shift+abs(x)) for x in cl])
    flags=list(range(f.nv+1,f.nv+2+hi-lo));f.append(flags)
    for d,z in zip(range(lo,hi+1),flags):
        for i in range(d-1,d+2):
            for j in range(30):
                if j%3:f.extend([[-z,-X[n*i+j]],[-z,-X[n*i+n-1-j]]])
    groups=[]
    for east in (False,True):
        gs=[]
        for t in range(6):
            vs=[X[n*i+(n-1-j if east else j)] for i in (3*t+1,3*t+2) if i<=16 for j in (6,7,8)]
            g=f.nv+1
            for x in vs:f.append([-x,g])
            f.append([-g,*vs]);gs.append(g)
        for g in gs:f.append([h for h in gs if h!=g])
        groups+=gs
    westonly='--west-only' in sys.argv
    f.extend(CardEnc.atmost(groups[:6] if westonly else groups,cap,top_id=f.nv).clauses)
    tag=('_west' if westonly else '')+('_reroot' if '--reroot' in sys.argv else '')
    absent=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--both-omit=')),None)
    if absent is not None:
        assert 0<=absent<6
        for g in (groups[absent],groups[6+absent]):f.append([-g])
        tag+=f'_bothomit{absent}'
    prefix=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--both-prefix=')),None)
    if prefix is not None:
        assert 3<=prefix<=6 and not westonly
        for gg in (groups[:6],groups[6:]):
            f.extend([[-v] for v in gg[prefix:]])
            f.extend(CardEnc.atleast(gg[:prefix],3,top_id=f.nv).clauses)
        tag+=f'_both3prefix{prefix}'
    allowed=next((s.split('=')[1] for s in sys.argv if s.startswith('--pairs=')),None)
    if allowed is not None:
        assert westonly and cap==2
        pairs={tuple(map(int,p)) for p in allowed.split(',')}
        from itertools import combinations
        assert pairs<=set(combinations(range(6),2))
        for a,b in combinations(range(6),2):
            if (a,b) not in pairs:f.append([-groups[a],-groups[b]])
        f.extend(CardEnc.atleast(groups[6:],3,top_id=f.nv).clauses)
        tag+='_p'+allowed.replace(',','-')
    if '--catalogue' in sys.argv:
        from pysat.solvers import Solver
        assert westonly and cap==2
        f.extend(CardEnc.atleast(groups[6:],3,top_id=f.nv).clauses)
        survive=[]
        with Solver(name='cadical195',bootstrap_with=f.clauses) as solver:
            while True:
                solver.conf_budget(5000)
                if solver.solve_limited() is not True:break
                model=set(solver.get_model());pair=tuple(i for i,x in enumerate(groups[:6]) if x in model)
                assert len(pair)==2 and pair not in survive;survive.append(pair)
                block=[-groups[i] for i in pair];solver.add_clause(block);f.append(block)
        print('crop-supported pairs',sorted(survive),flush=True)
        tag+='_catalogue'
    p=Path(f'target/offrail_corner_pair_{n}_{lo}_{hi}_{cap}{tag}.cnf');f.to_file(str(p))
    with p.with_suffix('.log').open('w') as fd:
        rc=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(p),str(p.with_suffix('.drat'))],stdout=fd).returncode
    if rc==20:
        out=subprocess.run(['target/drat-trim/drat-trim',str(p),str(p.with_suffix('.drat'))],check=True,capture_output=True).stdout
        assert b's VERIFIED' in out;p.with_suffix('.check').write_bytes(out);print(lo,hi,cap,'s VERIFIED')
    else:print(lo,hi,cap,'crop SAT' if rc==10 else 'UNKNOWN')
if __name__=='__main__':test(*map(int,sys.argv[1:6]))
