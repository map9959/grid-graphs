"""Proof-producing side-413 test on a nested physical overlap support."""
import sys,subprocess,hashlib
from pathlib import Path

D=Path('target/core371_lift')
def test(k,sec,kind=''):
    assert kind in ('','face','primal');suffix='_'+kind if kind else ''
    p=D/f'halo_{k}{suffix}.cnf';pr=p.with_suffix('.drat')
    subprocess.run(['target/core_halo',str(D/f'ranks{suffix}.bin'),str(k),'target/two_gap_413_0011_axis_ordinary_linked.cnf',str(p)],check=True)
    with p.with_suffix('.log').open('wb') as fd:
        rc=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(p),str(pr)],stdout=fd).returncode
    if rc==20:
        chk=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],check=True,capture_output=True).stdout
        assert b's VERIFIED' in chk;p.with_suffix('.check').write_bytes(chk)
        with p.open('rb') as fd:print('input',hashlib.file_digest(fd,'sha256').hexdigest())
        print(*[s for s in chk.decode().splitlines() if 'resolution steps' in s or 's VERIFIED' in s])
    elif rc==10:print('overlap projection SAT')
    else:assert rc==0;print('UNKNOWN')
if __name__=='__main__':test(*map(int,sys.argv[1:3]),*sys.argv[3:])
