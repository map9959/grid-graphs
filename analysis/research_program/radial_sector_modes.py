"""Price the scalar radial strip's recurrent modes with the physical sector dual."""
from fractions import Fraction
from .diagonal_score import data,DIR
from .dense_joint_collar import comb

def sample(n):
    pos,patch,star,sc,budget=data(n,comb(n)+1)
    for lo,hi in [(585,585),(1,509),(9,489),(73,329)]:
        vals=[]
        for shift in range(3):
            choices=[(hi,hi)] if lo==hi else [(hi|a,hi|b) for a in (0,512) for b in (0,512)]
            low=None
            for v,z in choices:
                def m(y,x):
                    h=lo if (x-shift)%3 else (v if (x-shift)%6==0 else z)
                    return h>>y&1
                cost=0
                for x in range(36,42):
                    for y in range(8):
                        bits=sum(m(y+i,x+j)<<(3*i+j) for i in range(3) for j in range(3))
                        cost+=patch(pos(y,x,1))[bits]
                    for y in range(9):
                        dirs=tuple(i for i,(u,w) in enumerate(DIR) if y+u>=0)
                        k=m(y,x)+sum(m(y+DIR[i][0],x+DIR[i][1])<<(j+1) for j,i in enumerate(dirs))
                        tab=star(pos(y,x,0),dirs,False)
                        cost+=min(v[k] for v in tab.values())
                low=cost if low is None else min(low,cost)
            vals.append(Fraction(low,6*sc))
        print(n,'budget',Fraction(budget,sc),'masks',lo,hi,'six-column minimum phase costs',vals,flush=True)
if __name__=='__main__':sample(103)
