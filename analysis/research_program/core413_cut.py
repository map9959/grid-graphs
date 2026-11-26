"""Induce a necessary overlap model on six finite blocks by deleting three seams."""
from array import array
from pathlib import Path
import sys,subprocess,hashlib
from .core413_seams import D

N=413
def run(row,left,right,sec):
    assert 16<=left<=104 and 308<=right<N-16 and 16<=row<N-16
    a=array('I');a.frombytes((D/'loc.bin').read_bytes());assert len(a)==2716318
    p=D/f'cut_{row}_{left}_{right}.cnf';r=p.with_suffix('.bin')
    allow=bytearray(len(a))
    for z,t in enumerate(a):
        i,j=(t>>16)-1,(t&65535)-1
        if min(abs(i-row),abs(j-left),abs(j-right))<=2:allow[z]=1
    r.write_bytes(allow)
    subprocess.run(['target/core_halo',str(r),'0','target/two_gap_413_0011_axis_ordinary_linked.cnf',str(p)],check=True)
    r.unlink()
    pr=p.with_suffix('.drat')
    with p.with_suffix('.log').open('wb') as fd:
        rc=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(p),str(pr)],stdout=fd).returncode
    if rc==20:
        chk=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],check=True,capture_output=True).stdout
        assert b's VERIFIED' in chk;p.with_suffix('.check').write_bytes(chk)
        with p.open('rb') as fd:print('verified cut',hashlib.file_digest(fd,'sha256').hexdigest())
    elif rc==10:print('cut model SAT')
    else:assert rc==0;print('UNKNOWN')
if __name__=='__main__':run(*map(int,sys.argv[1:]))
