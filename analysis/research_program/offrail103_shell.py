"""Min deletions from the 103 comb forced by the depth-nine score cuts alone."""
from pathlib import Path
import subprocess,sys
from pysat.card import CardEnc
from pysat.formula import CNF,IDPool
from pysat.solvers import Solver
from .comb_cap_transfer import construct
from .extend_forest_28 import verify

def run():
    n=103;rows=construct(n,4);print('donor tree',verify(rows),flush=True)
    marked={(i,j) for i in range(n) for j in range(n) if rows[i][j]=='#'}
    assert len(marked)==3646
    budget=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--exchange=')),2 if '--exchange' in sys.argv else None)
    whole=budget is not None
    for cap in ([budget] if whole else range(9)):
        f=CNF();vp=IDPool();X=lambda p:vp.id(('mark',p))
        # Only the boundary collars and diagonal blockers can enter
        # these necessary conditions. All other marks may change freely.
        collar={(i,j) for i in range(n) for j in range(n) if min(i,j,n-1-i,n-1-j)<=10}
        region=collar|{(i+x,j+y) for i,j in collar for x in (-1,1) for y in (-1,1)
                       if 0<=i+x<n and 0<=j+y<n}
        if whole:region={(i,j) for i in range(n) for j in range(n)}
        for i,j in sorted(region):
            for b in (-1,1):
                t=(i+1,j+b)
                if t in region:f.append([-X((i,j)),-X(t)])
        for transpose in (False,True):
            side=vp.id(('side',transpose))
            for far in (0,1):
                for d in range(10):
                    pts=[(n-1-i if far else i,j) for i in range(max(0,d-1),d+2) for j in range(n) if j%3]
                    f.append([side if far else -side,*[X((j,i) if transpose else (i,j)) for i,j in pts]])
        keep=sorted(marked&region)
        f.extend(CardEnc.atmost([-X(p) for p in keep],cap,vpool=vp).clauses)
        if whole:
            # A target with exactly cap deletions needs cap+1 additions.
            # At-most cap deletions only weakens that branch.
            extra=[X(p) for p in sorted(region-marked)]
            prev=[]
            for lit in extra:
                cur=[vp.id() for _ in range(min(cap+1,len(prev)+1))]
                for j,u in enumerate(cur):
                    clause=[-u]+prev[j:j+1]
                    f.append(clause+[lit])
                    if j:f.append(clause+[prev[j-1]])
                prev=cur
            f.append([prev[-1]])
            from .sector_matching import add
            add(f,vp,[X(divmod(i,n)) for i in range(n*n)],n)
            stem=Path(f'target/offrail103_exchange{cap}');cnf=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
            f.to_file(str(cnf))
            with stem.with_suffix('.log').open('wb') as fd:
                rc=subprocess.run(['target/cadical/build/cadical','-t','90',str(cnf),str(pr)],stdout=fd).returncode
            if rc==20:
                out=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(pr)],capture_output=True,check=True).stdout
                assert b's VERIFIED' in out;stem.with_suffix('.check').write_bytes(out)
                print('deletions',cap,'score-3647 search s VERIFIED')
            elif rc==10:
                model={int(v) for l in stem.with_suffix('.log').read_text().splitlines() if l.startswith('v ') for v in l[2:].split()}
                marks=[''.join('#' if X((i,j)) in model else '.' for j in range(n)) for i in range(n)]
                proof=verify(marks);assert proof[-1]>=3647;print('spanning tree',proof)
                stem.with_suffix('.txt').write_text('\n'.join(marks)+'\n')
            else:print('deletions',cap,'search UNKNOWN')
            return
        with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
            if s.solve():
                m=set(s.get_model());gone=[p for p in keep if X(p) not in m]
                print('first locally feasible budget',cap,'deleted',gone,'(not a score witness)')
                if '--pair-cover' not in sys.argv:return
                assert cap==2;found=[]
                while True:
                    m=set(s.get_model());pair=tuple(p for p in keep if X(p) not in m)
                    assert len(pair)==2 and pair not in found;found.append(pair)
                    block=[X(p) for p in pair];s.add_clause(block);f.append(block)
                    if not s.solve():break
                import json
                Path('target/offrail103_pairs.json').write_text(json.dumps(sorted(found))+'\n')
                print('locally feasible pairs',len(found),flush=True)
        stem=Path(f'target/offrail103_collar_d{cap}'+('_cover' if cap==2 else ''));cnf=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
        f.to_file(str(cnf))
        with stem.with_suffix('.log').open('wb') as fd:
            assert subprocess.run(['target/cadical/build/cadical',str(cnf),str(pr)],stdout=fd).returncode==20
        out=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(pr)],capture_output=True,check=True).stdout
        assert b's VERIFIED' in out;stem.with_suffix('.check').write_bytes(out)
        print('collar deletions <=',cap,'of',len(keep),('outside pair cover' if cap==2 else ''),'s VERIFIED',flush=True)
        if cap==2:return
if __name__=='__main__':run()
