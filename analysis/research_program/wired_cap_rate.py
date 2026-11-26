"""Rebuild the three transducers for the all-height/all-width 1/10 wired cap price."""
import os
from pathlib import Path
import subprocess
from .pitch_oriented_language import test

def audit(ranked=False):
    # Every filter must be necessary on its indicated interval, not
    # merely a frequent word. Indexing below is by pitch triples.
    specs=[
        ('start',3,2,[(1,0,0),(2,1,0),(2,2,1)]),
        ('step',7,6,[(2,2,0),(2,1,2),(3,2,2),(5,4,2),(2,2,5)]),
        ('stop',7,5,[(2,2,0),(2,1,2),(3,2,2),(5,3,2)])]
    env={k:v for k,v in os.environ.items() if not k.startswith('PITCH_')}
    if ranked:
        env.update(PITCH_RANK='1',PITCH_SCALE='1',PITCH_DEBIT='1')
        # Price one per waived sink. A literal eight-window check covers
        # a stop immediately after the initial three, then retain an
        # actual first neutral five before starting the language loop.
        first=[(3,2,0),(2,1,0),(1,0,0),(2,1,3),(3,2,3)]
        a=[8,5,350000,*[v for row in first+[(5,3,3)] for v in row]]
        # Run this after verifying the two elementary lower bounds below.
        specs[0]=('start',8,6,first+[(5,4,3),(2,2,6)])
        specs[1][3].extend([(4,3,0),(5,4,0)])
    # The recursive support filters use these small, disjoint-interval
    # lower bounds. No bounds for widths 7 or 8 are needed in a subcall
    # of size at most 5.
    for k,c in ((2,0),(3,1)):
        z=subprocess.check_output(['target/pitch_endpoint_tariff',str(k),str(c)],env=env,text=True)
        assert f'min(bill,{c+1})={c+1}' in z
    if ranked:
        z=subprocess.check_output(['target/pitch_endpoint_tariff',*map(str,a)],
                                  env={**env,'PITCH_FILTER_AUTO':'1'},text=True)
        assert 'state limit' not in z and 'min(bill,6)=6' in z
    for name,k,c,filters in specs:
        a=[k,c,350000,*[v for row in filters for v in row]]
        p=Path(f'target/pitch_{name}.nfa')
        with p.open('w') as f:
            subprocess.run(['target/pitch_endpoint_tariff',*map(str,a)],check=True,stdout=f,
                env={**env,'PITCH_NFA':f'{k},{c},2','PITCH_FILTER_AUTO':'1'})
        out=p.read_text()
        assert 'state limit' not in out and '\nNFA ' in out
    assert test(start=8 if ranked else 3,ranked=ranked)
    print('arbitrary cap: 20b <= 6r+15j' if ranked else 'every periodic wired cap: 10 * bonus <= 3 * pitch triples')

if __name__=='__main__':
    import sys
    audit('--rank' in sys.argv)
