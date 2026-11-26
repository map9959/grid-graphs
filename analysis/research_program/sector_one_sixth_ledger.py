"""Replay the all-size 1/6 equality case split and physical comb witnesses."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from unittest.mock import patch
import sys
from .diagonal_chart import run as chart
from .sector_phase_gaps import test as gaps
from .sector_component_charge import run as sink
from .sector_stripe_cover import run as cover
from .comb_cap_transfer import construct
from .extend_forest_28 import verify

def run(n):
    assert n in (67,76)
    base=55 if n==67 else 58
    k=n//3;target=(3*k*k+(32*k-7)//6,12*k+Q(68,3),24)
    def replay(options,strict=True):
        with patch.object(sys,'argv',['replay','--replay',*options]):
            a,b,c=chart(base,n,4,4)
        assert c==target[2] and b<=target[1] and (a<target[0] if strict else a==target[0])
    with patch.object(sys,'argv',['replay','--deep']):sink(base)
    for case in ('two','bare'):
        assert b's VERIFIED' in Path(f'target/sector_tight_windows_{n}_12_{case}.check').read_bytes()
    replay(['--corners=3'],False)
    cover(n)
    if n==76:
        assert b's VERIFIED' in Path('target/sector_diagonal_148_73_73_three_phase.check').read_bytes()
    for p in ([0,1] if n==67 else [0]):
        replay(['--corners=3','--sinks=connected',f'--phase={p}'])
    args=['--corners=4','--sinks=connected']
    replay([*args,'--band-debits=1,10'])
    gaps(5,2)
    for p in range(3):
        opts=[*args,f'--phase={p}','--pure-only','--arms=0','--phase-scope=quadrant','--arm-max=2']
        if n!=76 or p!=0:opts.append('--arm-bits')
        replay(opts)
    print('all cases excluded at',n,'+18t',flush=True)
    for N in (n,n+18):
        K=N//3;tree=verify(construct(N,4));assert tree[0]==tree[-1]==3*K*K+(32*K-7)//6-1
        print('physical spanning tree',N,tree)
if __name__=='__main__':run(int(sys.argv[1]))
