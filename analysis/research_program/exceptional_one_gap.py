"""Canonical one-gap physical board: common axis plus crop-root colors."""
from itertools import product
from pathlib import Path
import subprocess,sys
from .two_gap_board import Stream
from .defect_window import window,table
from .slit_star_transfer import frame_path
from .saturated_tile_phase import axis_clauses
from .extend_forest_28 import verify

def test(n,lo,hi,step,seconds):
    assert n%42==35 and 5<=lo<=hi<=n-6 and lo%3==2 and step in (3,6)
    M,A=frame_path(n,3)  # canonical 0133, rooted at SE
    assert A[n-1,n-1]==-1
    ds=range(lo,hi+1,step);sites={('s',2,d) for d in ds}
    p=Path(f'target/canonical_gap_{n}_{lo}_{hi}_{step}.cnf')
    f=Stream(p)
    def emit(f,bit,flags,arc,sheet):
        assert set(flags)==sites
        for pos,b in M.items():f.append([bit(*pos)*(1 if b else -1)])
        axis_clauses(f,bit,n)
        top=f.nv
        def color(i,j,h):return top+1+2*((n-4)*(i-2)+j-2)+h
        for i,j in product(range(2,n-2),repeat=2):
            z=bit(i,j)
            if min(i,j,n-1-i,n-1-j)==2:
                side=0 if i==2 else 1 if j==n-3 else 2 if i==n-3 else 3
                for h in (0,1):f.append([-z,color(i,j,h)*(1 if side>>h&1 else -1)])
            for x,y in ((i+1,j),(i,j+1)):
                if max(x,y)>n-3:continue
                for h in (0,1):
                    a,b=color(i,j,h),color(x,y,h)
                    for m in (z,bit(x,y)):f.extend([[-m,-a,b],[-m,a,-b]])
        f.to_file(str(p));print('one gap distances',ds,'vars',f.nv,'clauses',f.count,flush=True)
        with p.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(p),str(p.with_suffix('.drat'))],stdout=fd).returncode
        if rc==20:
            chk=subprocess.run(['target/drat-trim/drat-trim',str(p),str(p.with_suffix('.drat'))],capture_output=True,check=True).stdout
            assert b's VERIFIED' in chk;p.with_suffix('.check').write_bytes(chk);print('s VERIFIED')
        elif rc==10:
            model={int(x) for l in p.with_suffix('.log').read_text().splitlines() if l.startswith('v ') for x in l.split()[1:]}
            rows=[''.join('#' if bit(i,j) in model else '.' for j in range(n)) for i in range(n)]
            replay=verify(rows);k=(n-2)//3;assert replay[0]==replay[-1]==3*k*k+7*k-(k-5)//7
            p.with_suffix('.tree').write_text('\n'.join(rows)+'\n');print('physical tree',replay)
        else:assert rc==0;print('UNKNOWN');p.with_suffix('.drat').unlink(missing_ok=True)
    window(n,'rim',n,table(n),matching=True,root_site=(n-1,n-1),orient=A,emit_graph=emit,
           defects=sites,outward_completion=True,clause_sink=f)
if __name__=='__main__':test(*map(int,sys.argv[1:]))
