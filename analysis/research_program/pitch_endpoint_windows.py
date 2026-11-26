"""Replay all-height five-triple bill exclusion including the terminal signatures."""
import ast
import os
import subprocess

def window(k,limit,filters=()):
    a=['target/pitch_endpoint_tariff',k,limit,350000,*filters]
    env={**os.environ,'PITCH_TAILS':'1'};env.pop('PITCH_NO_RETURN',None)
    out=subprocess.check_output(list(map(str,a)),env=env,text=True)
    assert 'state limit' not in out
    bills={}
    for l in out.splitlines():
        if l.startswith('tail '):
            sig,c=l[5:].rsplit(' ',1);bills[tuple(ast.literal_eval(sig))]=int(c)
    return bills

def check():
    assert min(window(2,1).values())==1
    assert min(window(3,2).values())==2
    # If five cost at most three, each disjoint 2+3 or 3+2 split
    # attains its two individual lower bounds. Filter only by necessary
    # row transitions on accepting paths on these four projections.
    bills=window(5,3,(2,1,0,3,2,2,3,2,0,2,1,3))
    assert bills=={(48,56,56,56,56):3,(56,56,56,56,24):3,(56,)*5:3}
    print('all heights, five triples below four units:',bills)
    assert not window(7,4,(3,2,0,4,2,3,4,2,0,3,2,4))
    assert not window(8,5,(3,2,0,5,3,3,5,3,0,3,2,5))
    out=subprocess.check_output(['target/pitch_endpoint_tariff','18','13','350000'],
        env={**{z:v for z,v in os.environ.items() if not z.startswith('PITCH_')},'PITCH_AUTO':'1'},text=True)
    assert 'state limit' not in out and 'window 18 pitch triples, all heights: min(bill,14)=14' in out
    print('unconditional: 18 triples cost at least 14; bonus/width <= 11/108')

if __name__=='__main__':check()
