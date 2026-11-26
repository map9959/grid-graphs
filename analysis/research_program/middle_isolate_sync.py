"""Axis 1 can switch to the axis-2 catalogue *below* the north wave."""
from .coupled_mask_check import check
from .synchronous_grid import domains,unpack
from .synchronous_front import attempt

def audit():
    K=81;q=(25,55)
    for gx,gy,b in ((60,48,14),(60,60,1)):
        ds,g=domains(1,K,q,gx,gy,b)
        allowed=[frozenset(map(unpack,t)) for t in ds]
        def inspect(pool,actual):
            for i,j in set(zip(actual,g)):assert pool.items[i]<=allowed[j]
        assert not check(1,K,q,gx=(gx,),gy=(gy,),block=b,rounds=12,inspect=inspect)
        if b==14:
            for y in range(27,K-1):
                for x in range(K-1):
                    for h,ms in enumerate(zip(*allowed[g[y*(K-1)+x]])):
                        u,v=x+h//2,y+h%2
                        if v>=28 and min(u,v,K-1-u,K-1-v)>=4:
                            assert all(not (m&16 and m&40) for m in ms)
    for native in (True,False):
        assert attempt(2,K,28,4,8,60,60,6,25,True,native,[q],1)
    print('axis 1: q=25..55 excluded below row 28 on every exceptional k>=207')
if __name__=='__main__':audit()
