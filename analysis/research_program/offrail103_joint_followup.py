"""Check the full-board-only provisional negatives against the corner relaxation."""
import json,subprocess
from pathlib import Path
from .offrail103_pair_sweep import build

def test():
    dest=Path('target/offrail103_joint35')
    crop,board=[json.loads((dest/n).read_text()) for n in ('crop_750.json','board_500.json')]
    base,f,cases=build(True,False,joint=True)
    keys=[k for k,v in board.items() if v=='pending proof' and crop[k]!='VERIFIED UNSAT' and '2' in k[2:]]
    base.extend(f.clauses)
    for depth in (3,5):
        ks=[k for k in keys if k.startswith(f'{depth}:')]
        if not ks:continue
        base.append([cases[depth,k.split(':')[1]] for k in ks])
        path=dest/f'followup{depth}.cnf';base.to_file(str(path));base.clauses.pop()
        with path.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t','60',str(path),str(path.with_suffix('.drat'))],stdout=fd).returncode
        if rc==20:
            data=subprocess.run(['target/drat-trim/drat-trim',str(path),str(path.with_suffix('.drat'))],check=True,capture_output=True).stdout
            assert b's VERIFIED' in data;path.with_suffix('.check').write_bytes(data)
            path.with_suffix('.json').write_text(json.dumps(ks)+'\n')
        print(depth,len(ks),rc)
if __name__=='__main__':test()
