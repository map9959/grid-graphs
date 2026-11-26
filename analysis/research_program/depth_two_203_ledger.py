"""Replay the exact side-203 NW defect disjunctions; count physical sites once."""
from hashlib import file_digest
from fractions import Fraction
from itertools import product
from pathlib import Path
import subprocess,sys
from .odd_frames import frame,DIR
from .zipper_rails import build
from .extend_forest_28 import verify

CERTS=[
    (104,8,98,'star_rim_203_8_102_1_rim_base_0111',
     '58cb9aefadb04ef5105c10a9d43bcea85aab2358c30d25d7319b24d606f5c5a9'),
    (149,104,146,'depth_two_triangle_203_2_146_plus-1_from104',
     '5997fcff6a04cced483ac535e7cac52780e92f1415397f5b981431d4d2fae1b8'),
    (173,152,170,'depth_two_triangle_203_2_170_plus-1_from152',
     '4eafe6ce637265a57e7f41c658d5010fa1e4bf536df832209d38f10999ac2d82'),
    (197,176,194,'depth_two_triangle_203_2_194_plus-1_from176',
     '15d61eabdb6abf5f5c0ce89de7e49b75225ab40b885245a912f09ba3b47d246b')]
FAR=[
    (5,5,'ed21cfa735106081567eb7d796c0e1336d472692400df0561e08296c98fb3ba0'),
    (11,53,'04e6357b7863b4676f23147e21977fec968203af94345c5fb35e63963df03de9'),
    (59,101,'72f60afdf57dbefe8007371315e3fe60b72ddb199fbe611d3aa161d18a262c73'),
    (107,149,'808ecd4e576334f7ef0f75346a4bbaa4c53117065a2a6344372a53bcbbc12cca'),
    (155,197,'f6121a7eda07d8868804ae07b3c40dbcbae3a12796ea952976656e7c0053d4c0')]

def checked(name,digest):
    stem=Path('target')/name;cnf=stem.with_suffix('.cnf');check=stem.with_suffix('.check')
    with cnf.open('rb') as f:assert file_digest(f,'sha256').hexdigest()==digest
    if '--trim' in sys.argv and not stem.with_suffix('.trimcheck').exists():
        drat=stem.with_suffix('.drat');small=stem.with_suffix('.small')
        with stem.with_suffix('.trimming').open('wb') as out:
            subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(drat),'-C','-l',str(small)],stdout=out,check=True)
        with stem.with_suffix('.trimcheck').open('wb') as out:
            subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(small)],stdout=out,check=True)
        assert b's VERIFIED' in stem.with_suffix('.trimcheck').read_bytes()
        print('verified compact DRAT',name,drat.stat().st_size,'->',small.stat().st_size,flush=True)
        small.replace(drat)
    if '--drat' in sys.argv or not check.exists():
        with check.open('wb') as out:subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(stem.with_suffix('.drat'))],stdout=out,check=True)
    assert b's VERIFIED' in check.read_bytes()

def boundary(n,w):
    values=frame(n,(0,*w));p={(0,0):-1};q=list(p)
    for i,j in q:
        for d,(a,b) in enumerate(DIR):
            u=i+a,j+b
            if u in values and min(*u,n-1-u[0],n-1-u[1])==0 and u not in p and (values[i,j] or values[u]):
                p[u]=(d+2)%4;q.append(u)
    assert len(p)==4*n-4
    return values,p

def run():
    n=203;frames=[boundary(n,w) for w in product((1,3),repeat=3)]
    sites={(i,j) for d in range(5,n-5,3) for i,j in ((2,d),(d,2))}
    for side,lo,hi,name,digest in CERTS:
        for k in (0,1):
            assert len({tuple(sorted((u,b) for u,b in m[k].items() if max(u)<side)) for m in frames})==1
        checked(name,digest)
        gone={(i,j) for d in range(lo,hi+1,6) for i,j in ((2,d),(d,2))}
        assert gone<=sites and hi+2<side
        sites-=gone
        print('s VERIFIED',f'{side}x{side}',f'{lo}..{hi} step 6',len(gone),'sites, common to eight frames')
    reflected=[{(j,i):b for (i,j),b in m.items()} for m,_ in frames]
    assert len({frozenset(m.items()) for m in [*(m for m,p in frames),*reflected]})==16
    for lo,hi,digest in FAR:
        checked(f'depth_two_far_quarter_203_{lo}_{hi}',digest)
        gone={(i,j) for d in range(lo,hi+1,6) for i,j in ((2,d),(d,2))}
        assert gone<=sites and lo%6==hi%6==5
        sites-=gone
        print('s VERIFIED three quarters',f'{lo}..{hi} step 6',len(gone),'sites, eight frames on each arm')
    print('remaining per frame:',len(sites),'by distance phase',
          {p:sum(max(u)%6==p for u in sites) for p in (2,5)})
    lower=verify(build(n));print('physical lower-bound spanning tree:',lower)
    ub=Fraction(n*n,3)+Fraction(20*n,21)-Fraction(67,42)
    assert ub==13928+Fraction(1,14) and lower==(13927,41207,2,41208,13927)
    if not sites:
        # The other branch is the previously proved unrestricted-depth
        # two-gap exclusion, together with the five uniform rim exclusions.
        base=Path('target/interior_connector_203.cnf')
        with base.open('rb') as f:assert file_digest(f,'sha256').hexdigest()=='7ff44e7e0ba2f87b9f2d7035f665c7fad58be1166a5a920dfec39fa914ad5bd5'
        assert b's VERIFIED' in base.with_suffix('.check').read_bytes()
        print('two-gap certificate matches; upper equality case exhausted: P(203,203)=13927')
if __name__=='__main__':run()
