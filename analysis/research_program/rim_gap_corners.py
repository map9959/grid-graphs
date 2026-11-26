"""Price the maximal perimeter gap branch with the actual corner sinks."""
from itertools import product
from pathlib import Path
from subprocess import run
from .diagonal_score import data,generate

def audit(n,g):
    k=n//3;t=3*k*k+(16*k-7)//3
    tables=data(n,t)
    for size in (10,15,19,24):
        f,X=generate(n,t,set(product(range(size),repeat=2)),False,tables)
        p=Path(f'target/rim_gap_corner_{n}_{g}');cnf=p.with_suffix('.cnf');pr=p.with_suffix('.drat')
        f.to_file(str(cnf));res=run(['target/cadical/build/cadical','-t','20',str(cnf),str(pr)],capture_output=True)
        if res.returncode==20:
            check=run(['target/drat-trim/drat-trim',str(cnf),str(pr)],capture_output=True,check=True)
            assert b's VERIFIED' in check.stdout
            print('NW window',n,g,size,'s VERIFIED',flush=True);cnf.unlink();pr.unlink();return True
        cnf.unlink();pr.unlink(missing_ok=True)
    return False
if __name__=='__main__':
    import sys
    g=int(next(z.split('=')[1] for z in sys.argv if z.startswith('--rim-gaps=')))
    for n in (103,112):print('excluded?',audit(n,g))
