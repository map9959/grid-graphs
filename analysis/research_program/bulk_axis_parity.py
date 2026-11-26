"""Period-three unaveraged parity after imposing one common deep-bulk axis."""
from itertools import product
from .odd_charge_parity import build,possible,DIR
from .odd_frames import frame
import sys

def test(words):
    n=77;D=14;cols,qs,rhs,nr,labels,rd,mass=build(n,3,depth=D)
    def ix(i,S,d):return i if i<d else 2*d+3+i-S if i>=S-d else d+(i-d)%3
    reps={}
    for t in range(2):
        for i,j in product(range(n-2*t),repeat=2):
            reps[t,ix(i,n-2*t,D-t),ix(j,n-2*t,D-t)]=i,j
    def bits(ls):
        v=0
        for r in ls:v^=1<<(r if r>=0 else ~r)
        return v
    print('period 3 depth 14; rows',nr,'columns',len(qs),flush=True)
    for word in words:
        gaps=sum(c in '02' for c in word)
        assert gaps in (1,2);f=frame(n,tuple(map(int,word)))
        path={(0,0):-1};todo=list(path)
        for u in todo:
            for d,(a,b) in enumerate(DIR):
                v=u[0]+a,u[1]+b
                if v not in path and v in f and min(*v,n-1-v[0],n-1-v[1])==0 and (f[u] or f[v]):
                    path[v]=(d+2)%4;todo.append(v)
        for horiz in (True,False):
            q=qs.copy()
            for h,(k,e) in enumerate(labels):
                i,j=reps[k];t=k[0];dep=min(i,j,n-1-i,n-1-j)
                if t:
                    ok=not q[h] and all(f.get((i+a,j+b),e>>(3*a+b)&1)==(e>>(3*a+b)&1) for a,b in product(range(3),repeat=2))
                    center=(i+1,j+1)
                    if all(14<=v<n-14 and v%3==2 for v in center) and e&16 and e&(40 if horiz else 130):ok=False
                else:
                    s,nb,o=e
                    ok=s==f.get((i,j),s) and o==path.get((i,j),o) and all(
                        nb[d]==f.get((i+a,j+b),nb[d]) for d,(a,b) in enumerate(DIR))
                    if dep>=14 and i%3==j%3==2 and s and any(nb[d]==1 for d in ((0,2) if horiz else (1,3))):ok=False
                    if q[h]:ok &= q[h]==72 and ((gaps==2 and dep==0 and (i,j) not in path) or
                            (gaps==1 and min(i,j)==2 and max(i,j)%3==2 and not s and nb.count(1)==0))
                if not ok:q[h]=73
            take=possible(cols,q,rd,mass,labels,(72,));piv={}
            def reduce(v):
                r=0
                while v:
                    z=v.bit_length()-1
                    if z in piv:v^=piv[z]
                    else:r^=1<<z;v^=1<<z
                return r
            for ls,v,kp in zip(cols,q,take):
                if not kp or v:continue
                z=bits(ls)
                while z and z.bit_length()-1 in piv:z^=piv[z.bit_length()-1]
                if z:piv[z.bit_length()-1]=z
            rem=reduce(bits(rhs))
            poss={k for (k,_),ls,v,kp in zip(labels,cols,q,take) if kp and v==72 and reduce(bits(ls))==rem}
            print(word,'no',('horizontal' if horiz else 'vertical'),'center pairs; surviving defect buckets',len(poss),sorted(poss),flush=True)
if __name__=='__main__':test(sys.argv[1:])
