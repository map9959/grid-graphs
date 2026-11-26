"""Audit the local proof inputs and both repeating covers for three corners."""
from functools import lru_cache
from itertools import product
from pathlib import Path
import subprocess,sys

def run(base):
    n0=base+72;c=(n0-2)//2
    refs={(i,i+h) for i,h in product((*range(7,19),24,25,26,*range(c-12,c+1)),(0,1))}
    # A translated halo preserves not only the mark stencil but each
    # location in every star and patch orbit (D4 permutes the signed clips).
    @lru_cache(None)
    def sig(n,i,j):
        def at(x,y,S,H):
            def ax(v):return v if v<H else 2*H+3+v-S if v>=S-H else H+(v-H)%3
            cl=lambda v:max(-9,min(9,v))
            return ax(x),ax(y),cl(x-y),cl(x+y+1-S)
        return tuple(at(i+a,j+b,n-2*q,8-q)
                     for q in (0,1) for a,b in product(range(-5,8-2*q),repeat=2))
    keys={sig(n0,i,j) for i,j in refs}
    for i,j in refs:
        p=Path(f'target/sector_diagonal_{n0}_{i}_{j}_three.cnf')
        assert b's VERIFIED' in p.with_suffix('.check').read_bytes()
        if '--drat' in sys.argv:
            s=subprocess.run(['target/drat-trim/drat-trim',str(p),str(p.with_suffix('.drat'))],capture_output=True,check=True)
            assert b's VERIFIED' in s.stdout
    for n in (base,base+18):
        for i,h in product(range(7,(n-2)//2+1),range(2)):
            assert sig(n,i,i+h) in keys,(n,i,h)
    # From the second base on, keep the first 22 origins fixed, move
    # the remaining origins nine places with the center. The nine new
    # origins in between have saturated second diagonal and axis labels.
    n=base+18
    for i,h in product(range(7,(n-2)//2+1),range(2)):
        z=0 if i<22 else 9
        assert sig(n,i,i+h)==sig(n+18,i+z,i+h+z)
    for i,h in product(range(22,31),range(2)):
        assert sig(n+18,i,i+h)==sig(n0,24+i%3,24+i%3+h)
    print(base,'+18t:',len(refs),'verified windows cover both diagonal staircases')
if __name__=='__main__':
    for b in (67,76):run(b)
