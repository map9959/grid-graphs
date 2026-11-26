"""All-pitch conditional bounds, using ghost endpoint classes on shifted cuts."""
import sys
from . import seam_rank_chart,seam_rank_cost
from fractions import Fraction as Q

def bound10(k,p,q):
    assert p!=0 or q!=0
    error=-k-2 if min(p,q)==0 else -6 if p==q else -k-5
    return (10*(3*k+1)*(k+1)+13*k+error+(-3 if p else -10)+(-13 if q else -10)
            -10*int(bool(p))-10*int(bool(q)))

def audit():
    orig=sys.argv[:]
    try:
        for p,q in ((1,0),(1,1),(1,2)):
            sys.argv=['rank',f'--top-phase={p}',f'--bottom-phase={q}','--price=7/10','--rank-both','--shifted-certificate','--replay','--matrix']
            seam_rank_chart.run(12,43,0)
        for n in range(94,124,3):
            k=n//3;r=k+1
            for p in (0,1,2):
                sys.argv=['cap','--free-top','--classes','--prices=10,7','--quiet',f'--lower-phase={p}']
                for h,constant in ((2,-3 if p else -10),(6,-13 if p else -10)):
                    vals,log=seam_rank_cost.run(n,h,[60,90])
                    assert max(vals.values())==10*h*r+7*r+3*k+constant
                    assert f'same true dominated true shift {100*h+100}' in log
        print('all boundary phases: exact upper prices and width-30 cap recurrences')
    finally:sys.argv=orig
if __name__=='__main__':audit()
