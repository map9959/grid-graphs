"""One-gap test, using the deep-bulk dichotomy and planar dual edge owners."""
from itertools import product
from pathlib import Path
import sys
from .depth_two_far_quarter import run
from .saturated_tile_phase import axis_clauses
from .extend_forest_28 import verify

def test(n,lo,hi,sec):
    dom=set(product(range(n),repeat=2))
    stem=f'target/bulk_axis_board_{n}_{lo}_{hi}'
    def extra(f,bit,flags):axis_clauses(f,bit,n)
    def replay(w,star,marks,out):
        rows=[''.join('#' if (i,j) in marks else '.' for j in range(n)) for i in range(n)]
        k=(n-2)//3;u=3*k*k+7*k-(k-5)//7
        result=verify(rows);assert result[0]==result[-1]==u
        Path(stem+'.tree').write_text('\n'.join(rows)+'\n');print(w,star,'physical spanning tree',result)
    run(n,lo,hi,sec,domain=dom,output=stem,replay=replay,extra=extra,turn_domain=set(),matching=True)
if __name__=='__main__':test(*map(int,sys.argv[1:]))
