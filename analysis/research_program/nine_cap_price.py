"""Close out every prefix and certify the depth-nine free-cap price."""
from unittest.mock import patch
import sys
from .seam_rank_cost import run

def prove():
    h=9;N=133
    with patch.object(sys,'argv',['check','--classes','--prices=10,7','--free-top','--quiet']):
        final,log=run(N,h,[90,120])
        assert 'same true dominated true shift 1000' in log
        with patch.object(sys,'argv',[*sys.argv,'--prefix']):
            compare,log=run(N,h,range(18,133,3))
        assert final==compare
        prefixes=[tuple(map(int,line.split()[2:])) for line in log.splitlines() if line.startswith('prefix ')]
        widths=list(range(19,134,3));assert len(prefixes)==len(widths)
        for n,(one,many) in zip(widths,prefixes):
            k=n//3;r=k+1
            assert one==10*h*r+10*(k-1)+7,(n,one)
            assert many<=10*h*r+3*k+7*r-13,(n,many)
        for n in (19,52,103,N):
            v,_=run(n,h) if n!=N else (final,'')
            assert prefixes[(n-19)//3]==(v[1],v[2])
        print('depth nine: all 39 prefix widths 19..133 pass; class maxima at 133:',final)
        print('columns 90 and 120: identical normalized frontier, shift 1000; extends to all widths 3k+1 >=19')
if __name__=='__main__':prove()
