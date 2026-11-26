"""Condition the pooled sector relaxation on the corner marginals of a cube."""
from .diagonal_chart import relaxation,Q,Counter,count,verify
from .side28_score import solve
from .patch_square import MASKS,SYM,trans
from .sector_perimeter_split import groups,rotate,sites,n
from itertools import product

def run():
    ns,rows,obj=relaxation(55,8,pooled=4,period=3,diagonal=4)
    inv={v:k for k,v in ns.items()}
    A=[];rhs=[]
    for row,op,b in rows:
        if b and op=='=':
            k,atom=inv[row[0][0]];tag=int(k=='p')
            b=count(n-2*tag,8-tag,9,atom[0])[0]
        A.append((row,op));rhs.append(b)
    # Marginals on the three physical cells in the NW corner patch,
    # averaged over all eight images; the corner bucket is a singleton.
    S=n-2
    def axis(x):return x if x<7 else 17+x-S if x>=S-7 else 7+(x-7)%3
    clip=lambda x:max(-9,min(9,x))
    pos=[(axis(i),axis(j),clip(i-j),clip(i+j+1-S)) for h in range(8) for i,j in [trans(0,0,S,h)]]
    cells={}
    for m in MASKS:
        key=(m&1,m>>1&1,m>>3&1)
        cells.setdefault(key,Counter())[ns['p',min(zip(pos,SYM[m]))]]+=1
    for w in ('011101010101','111101010101'):
        hist=Counter(tuple(int(rotate(w,h)[i]) for i in (0,4,5)) for h in range(8))
        mat=A+[(list(c.items()),'=') for c in cells.values()]
        b=rhs+[Q(hist[k],8) for k in cells]
        z,y,_=solve(mat,b,obj,ns,interior=True)
        print(w,'corner conditioned candidate',z,flush=True)
        if z<4078-1e-5:
            # Repair all dual residuals by positive normalization rows.
            Y={i:Q(round(float(x)*10**9),10**9) for i,x in enumerate(y) if x}
            balance=Counter(obj);norms={}
            for i,(cs,op) in enumerate(mat):
                v=Y.get(i,0)
                if op=='>=':v=min(0,v)
                if op=='<=':v=max(0,v)
                Y[i]=v
                for x,c in cs:
                    balance[x]-=c*v
                    if i<len(A) and rhs[i]>0 and op=='=':norms[x]=(i,c)
            repair=Counter()
            for x,gap in balance.items():
                if gap>0:
                    i,c=norms[x];repair[i]=max(repair[i],Q(gap,c))
            for i,v in repair.items():Y[i]+=v
            assert verify(mat,obj,Y)<=0
            bound=sum(b[i]*v for i,v in Y.items());print('rational upper',bound,flush=True)
if __name__=='__main__':run()
