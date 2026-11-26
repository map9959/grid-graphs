"""Two independent width-seven suffix transfers meet in the NW square.

Only marks are transferred. Each star chooses its own direction, and all
perimeter stars may pay. Thus a negative decision needs neither an arrow
partition, a charged-exit location, nor an external-terminal convention.
"""
from functools import lru_cache
from itertools import product
from .defect_window import table, DIR
from .odd_frames import frame

H=7

class Arm:
    def __init__(self,n,vertical,data,marks):
        self.n=n;self.v=vertical;self.typ,self.patch,self.star=data
        self.fixed=marks
        self.xy=lambda r,c:(c,r) if vertical else (r,c)

    @lru_cache(None)
    def cols(self,j):
        return tuple(m for m in range(128) if all((self.xy(r,j) not in self.fixed or
            m>>r&1==self.fixed[self.xy(r,j)]) for r in range(H)))

    @lru_cache(None)
    def ptab(self,r,j):
        return self.patch(self.typ(1,*self.xy(r,j)))

    @lru_cache(None)
    def stab(self,r,j):
        n=self.n;i,k=self.xy(r,j)
        ds=tuple(d for d,(dx,dy) in enumerate(DIR) if 0<=i+dx<n and 0<=k+dy<n)
        q=[self.star(self.typ(0,i,k),ds,o,o==-1,len(ds)==2) for o in [-1,*ds]]
        return [any(z==0 or (len(ds)<4 and z==72) for z in a) for a in zip(*q)]

    def legal(self,j,a,b,c,patches=True):
        if patches:
            for r in range(5):
                m=((a>>r&7) | (b>>r&7)<<3 | (c>>r&7)<<6)
                if not self.v:m=TRANS[m]
                if self.ptab(r,j-1)[m]:return False
        for r in range(6):
            bits=(c>>r&1,b>>(r+1)&1,a>>r&1,(b>>(r-1)&1) if r else 0)
            if self.v:bits=(bits[1],bits[0],bits[3],bits[2])
            i,k=self.xy(r,j)
            ds=(d for d,(dx,dy) in enumerate(DIR) if 0<=i+dx<self.n and 0<=k+dy<self.n)
            m=(b>>r&1)+sum(bits[d]<<(1+u) for u,d in enumerate(ds))
            if not self.stab(r,j)[m]:return False
        return True

    def suffix(self):
        n=self.n
        ok={(a,b) for a,b in product(self.cols(n-2),self.cols(n-1))
            if self.legal(n-1,a,b,0,False)}
        layers={n-2:ok}
        for j in range(n-2,5,-1):
            x=j if not 9<=j<n-9 else 9+(j%3)
            ok={(a,b) for b,c in ok for a in self.cols(j-1) if self.legal(x,a,b,c)}
            layers[j-1]=ok
        return layers

TRANS=[sum((m>>(3*c+r)&1)<<(3*r+c) for r,c in product(range(3),repeat=2)) for m in range(512)]

def emit():
    from pathlib import Path
    path=Path(__file__).resolve().parents[2]/'lean/GridGraphs/ResidueTwoUpper/Opposite0101'
    data=table(35);marks=frame(35,(0,1,0,1))
    states=[];tables=[]
    for v in [False,True]:
        arm=Arm(35,v,data,marks)
        l=arm.suffix()
        # Suffix recurrence ignores the leading corner's masks; ranks at
        # 5..23 are already periodic. Keep exact layers in the end halo.
        for j in range(5,34):
            states.append(' '.join(str(128*a+b) for a,b in sorted(l[j])))
        for j in range(35):
            ss=[]
            for r in range(6):
                i,k=arm.xy(r,j)
                ds=[d for d,(a,b) in enumerate(DIR) if 0<=i+a<35 and 0<=k+b<35]
                sl=arm.stab(r,j)
                ss.append(sum(1<<m for m in range(32) if all(not (m>>(1+d)&1) for d in range(4) if d not in ds)
                         and sl[(m&1)+sum((m>>(1+d)&1)<<(u+1) for u,d in enumerate(ds))]))
            ps=[sum(1<<m for m,z in enumerate(arm.ptab(r,j)) if not z) if j<33 else 0 for r in range(5)]
            tables.append(' '.join(map(str,ss+ps)))
    (path/'suffixes.txt').write_text('\n'.join(states)+'\n')
    (path/'stencils.txt').write_text('\n'.join(tables)+'\n')

def join(n,info=False):
    data=table(n);marks=frame(n,(0,1,0,1))
    A,B=[Arm(n,v,data,marks) for v in (False,True)]
    L,R=A.suffix(),B.suffix()
    if info:
        for layers in (L,R):
            print('layers',[(j,len(layers[j])) for j in sorted(layers) if j<21 or j>n-21],flush=True)
            print('three-phase stabilization',next((j for j in range(n-12,9,-1)
                    if layers[j]==layers[j-3]),None),flush=True)
    cnt=joincnt=0
    def go(seq):
        nonlocal cnt,joincnt
        j=len(seq)-1
        if j==6:
            if (seq[5],seq[6]) not in L[5]:return
            cnt+=1
            a,b=[sum(((v>>r)&1)<<k for k,v in enumerate(seq)) for r in (5,6)]
            if (a,b) in R[5]:joincnt+=1
            return
        for c in A.cols(j+1):
            a=seq[j-1] if j else 0
            if A.legal(j,a,seq[j],c,j>0):go(seq+(c,))
    for b in A.cols(0):go((b,))
    print(n,'disjoint corner words',cnt,'joint survivors',joincnt,flush=True)
    return L,R,joincnt

if __name__=='__main__':
    import sys
    if '--emit' in sys.argv:emit()
    else:
        for n in map(int,sys.argv[1:] or (35,77)):join(n,True)
