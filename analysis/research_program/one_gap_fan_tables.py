"""Audit the two short fan lookup arrays against the original local dual.
The corresponding Lean finite checks independently certify soundness.
"""
from pathlib import Path
from functools import lru_cache
import re
from .defect_window import table

ROOT=Path(__file__).resolve().parents[2]/'lean/GridGraphs/ResidueTwoUpper/OneGap'

def audit():
    typ,patch,star=table(35)
    seed=(ROOT/'FanSeedData.lean').read_text()
    words=[int(x,16) for x in re.findall(r'0x[0-9a-f]+',seed)]
    ids=list(map(int,re.search(r'ids : Array Nat := #\[(.*?)\]',seed,re.S)[1].split(',')))
    for r in range(5):
        for j in range(33):
            assert words[ids[33*r+j]]==sum(1<<m for m,z in enumerate(patch(typ(1,r,j))) if z==0)
    slab=[int(x,16) for x in re.findall(r'0x[0-9a-f]+',(ROOT/'FanSlabData.lean').read_text())]
    def cross(m):return (m>>4&1)+2*(m>>5&1)+4*(m>>7&1)+8*(m>>3&1)+16*(m>>1&1)
    for r in range(3):
        a=6+(1+r)%3
        for t in range(13):
            b=1+t if t<8 else 19+t
            ts=[star(typ(0,a+1,b+1),tuple(range(4)),o,o==-1,False) for o in (-1,0,1,2,3)]
            word=sum(1<<m for m,z in enumerate(patch(typ(1,a,b))) if z==0 and
                     (t<5 or t>=8 or any(row[cross(m)]==0 for row in ts)))
            assert slab[13*r+t]==word,(r,t)
    print('seed: 165 positions, 43 distinct words; slab: 39 labeled words')
if __name__=='__main__':audit()
