"""Keep compact checked DRAT streams and only one copy of each shared input."""
from pathlib import Path
import sys
from .southwest_ports_ledger import GROUPS,LOCAL,digest
from .southwest_port_core import checked
from .sw_port_batch import make

def run(local,a,b):
    for lo,hi,h in LOCAL if local else GROUPS:
        if not a<=lo<=hi<=b:continue
        stem=Path(f'target/sw_port_batch_{lo}_{hi}_5_191'+('_local' if local else ''))
        cnf=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
        if not cnf.exists():make(lo,hi,5,191,cnf,local)
        assert digest(cnf)==h
        small=stem.with_suffix('.small');recheck=stem.with_suffix('.compactcheck')
        if not recheck.exists() or b's VERIFIED' not in recheck.read_bytes():
            if not (lo==hi==150 and small.exists() and not local):
                checked(['target/drat-trim/drat-trim',str(cnf),str(pr),'-C','-l',str(small)],stem.with_suffix('.compactlog'))
            checked(['target/drat-trim/drat-trim',str(cnf),str(small)],recheck)
            print(stem.name,pr.stat().st_size,'->',small.stat().st_size,'verified',flush=True);small.replace(pr)
        cnf.unlink()
if __name__=='__main__':run(*map(int,sys.argv[1:]))
