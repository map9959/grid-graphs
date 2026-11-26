"""Does optimizing over rim-maximal representatives change the sector slope?"""
from collections import Counter
from .patch_square import relaxation
from .side28_score import solve
from .chart_counts import count

def test(n,base=55):
    from .rim_patch_dominance import cubes
    from .patch_square import SYM,trans
    from functools import lru_cache
    masks=cubes(4,4,True,True,True)
    seen={(i,j):{sum((m>>(4*(i+y)+j+x)&1)<<(3*y+x) for y in range(3) for x in range(3)) for m in masks}
          for i in range(2) for j in range(2)}
    @lru_cache(None)
    def allowed(i,j,m):
        for rot in range(4):
            y,x=trans(i,j,base-2,rot);word=SYM[m][rot]
            if (y,x) in seen and word not in seen[y,x]:return False
            if y==0:
                if x==base-3:continue  # the neighboring rotation handles this corner
                if any(word&k==v for k,v in cubes(3,3,x==0)):return False
        return True
    def accept(i,j,tag,v):
        if tag:return allowed(i,j,v)
        f,nb,_=v
        if f:return True
        if i in (0,base-1) and 2<=j<base-2:return not(nb[0]==nb[2]==1)
        if j in (0,base-1) and 2<=i<base-2:return not(nb[1]==nb[3]==1)
        return True
    names,rr,obj=relaxation(base,8,pooled=4,period=3,diagonal=4,accept=accept,group_override=tuple(range(4)))
    inv={v:k for k,v in names.items()};A=[];b=[]
    for row,op,rhs in rr:
        if rhs and op=='=':
            k,atom=inv[row[0][0]];p=int(k=='p');rhs=count(n-2*p,8-p,9,atom[0])[0]
        A.append((row,op));b.append(rhs)
    val,_,_=solve(A,b,obj,names,interior=True)
    print('side',n,'canonical singleton-free sector LP (numerical)',val,flush=True)
if __name__=='__main__':test(103)
