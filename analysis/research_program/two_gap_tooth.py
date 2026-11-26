"""Can the unique inter-arc bridge leave through a gap-corner tooth?"""
import sys,subprocess
from itertools import product
from pathlib import Path
from .defect_window import window,table
from .odd_frames import frame

def test(width,sec):
    n=119;dom=set(product(range(width),repeat=2));m=frame(n,(0,0,1,1))
    def emit(f,bit,flags,arc,sheet):
        assert set(flags)=={('s',2,0)}
        for u,v in m.items():
            if u in dom:f.append([bit(*u) if v else -bit(*u)])
        f.append([arc(2,0,0)]) # inward from the surviving west foot
        p=Path(f'target/two_gap_tooth_{width}.cnf');pr=p.with_suffix('.drat');f.to_file(str(p))
        with p.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(p),str(pr)],stdout=fd).returncode
        if rc==20:
            data=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],capture_output=True,check=True).stdout
            assert b's VERIFIED' in data;p.with_suffix('.check').write_bytes(data);print(width,'s VERIFIED')
        else:print(width,'crop SAT' if rc==10 else 'UNKNOWN')
    window(n,'rim',1,table(n),domain=dom,defects={('s',2,0)},root_site=(0,n-1),emit_graph=emit,matching=True)
if __name__=='__main__':test(*map(int,sys.argv[1:]))
