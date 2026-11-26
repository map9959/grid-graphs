"""Regenerate the physical score-661 formula; optionally solve and check its DRAT proof."""
import argparse
from hashlib import sha256
from pathlib import Path
import subprocess
from .side28_sat import cnf


def run(check):
    out=Path('target');out.mkdir(exist_ok=True)
    formula=out/'forest43.cnf';proof=out/'forest43.drat'
    f,_=cnf(43,scale=168,target=661)
    f.to_file(str(formula))
    print('side 43:',f.nv,'variables,',len(f.clauses),'clauses, sha256',
          sha256(formula.read_bytes()).hexdigest(),flush=True)
    if check:
        result=subprocess.run([str(out/'cadical/build/cadical'),str(formula),str(proof)],
                              stdout=subprocess.PIPE,text=True)
        assert result.returncode==20 and 's UNSATISFIABLE' in result.stdout.splitlines()
        log=out/'forest43.check'
        with log.open('w') as stream:
            subprocess.run([str(out/'drat-trim/drat-trim'),str(formula),str(proof)],
                           stdout=stream,check=True)
        assert 's VERIFIED' in log.read_text().splitlines()
        print('score 661 excluded: UNSATISFIABLE, independently VERIFIED')


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    run(parser.parse_args().check)
