"""Discrete perimeter signatures and a uniform characteristic-two support test."""
from .odd_charge_parity import build,possible
from .square_dual_physical import DIR,SYM,trans
from collections import Counter
from itertools import product
import sys

PAT=((0,0,1,1),(0,1,1,1),(1,1,0,0),(1,1,0,1))
PORT=((0,1),(0,2),(1,0),(2,0))
def frame(n,word):
    val={(i,j):int(min(i,j,n-1-i,n-1-j)==0) for i,j in product(range(n),repeat=2) if min(i,j,n-1-i,n-1-j)<2}
    for g,w in enumerate(word):
        for u,v in zip(PORT,PAT[w]):val[trans(*u,n,g)]=v
    return val
def rotate(word,h):
    n=35;b=frame(n,word);m={trans(*u,n,h):v for u,v in b.items()}
    return tuple(PAT.index(tuple(m[trans(*u,n,g)] for u in PORT)) for g in range(4))
def prep():
    cols,q,_,_,labels,rd,mass=build(35)
    take=possible(cols,q,rd,mass,labels,(72,))
    for i,z in enumerate(take):
        if not z:q[i]=73
    bits=[]
    for cs in cols:
        v=0
        for r in cs:v^=1<<(r if r>=0 else ~r)
        bits.append(v)
    target=[]
    for n in (35,77):
        b=0
        for key in mass:
            tag,r,c=key;h=6-tag
            ct=lambda z:(n-2*tag-2*h+5-(z-h))//6 if h<=z<h+6 else 1
            if ct(r)*ct(c)%2:b^=1<<rd['norm',key]
        target.append(b) # U is even
    return cols,q,labels,rd,mass,bits,target

def evaluate(data,word):
    n=35;cols,q,labels,rd,mass,bits,target=data;v=frame(n,word)
    def boundary(i,j):return min(i,j,n-1-i,n-1-j)==0
    par={(0,0):-1};todo=[(0,0)]
    for i,j in todo:
        for d,(a,b) in enumerate(DIR):
            z=i+a,j+b
            if z in v and boundary(*z) and z not in par and (v[i,j] or v[z]):
                par[z]=(d+2)%4;todo.append(z)
    # Every vertex in the perimeter component of NW must follow its
    # unique path in that component, including for a larger square.
    def coord(i,S,h):return i if i<h else 2*h+6+i-S if i>=S-h else h+(i-h)%6
    loc={key:[] for key in mass}
    for t in range(2):
        S=n-2*t;h=6-t
        for i,j in product(range(S),repeat=2):loc[t,coord(i,S,h),coord(j,S,h)].append((i,j))
    # Boundary words and prescribed arrows are constant over each bucket.
    signs={}
    def known(t,i,j):
        if t:return tuple(v.get((i+a,j+b)) for a,b in product(range(3),repeat=2))
        return (v.get((i,j)),*(v.get((i+a,j+b)) for a,b in DIR),par.get((i,j)))
    for key,sites in loc.items():
        vv={known(key[0],i,j) for i,j in sites};assert len(vv)==1;signs[key]=vv.pop()
    qq=q.copy()
    for i,(key,e) in enumerate(labels):
        if qq[i]>72:continue
        if key[0]:uu=tuple((e>>h)&1 for h in range(9))
        else:uu=(e[0],*e[1],e[2])
        if any(a is not None and a!=b for a,b in zip(signs[key],uu)):qq[i]=73
    take=possible(cols,qq,rd,mass,labels,(72,))
    if not take:return [[],[]]
    piv={}
    for b,ok,c in zip(bits,take,qq):
        if not ok or c:continue
        while b:
            j=b.bit_length()-1
            if j not in piv:piv[j]=b;break
            b^=piv[j]
    def rem(b):
        v=0
        while b:
            j=b.bit_length()-1
            if j in piv:b^=piv[j]
            else:v^=1<<j;b^=1<<j
        return v
    rr=[(rem(b),e) for b,ok,c,e in zip(bits,take,qq,labels) if ok and c==72]
    return [[e for r,e in rr if r==z] for z in map(rem,target)]

def run():
    data=prep();cache={};surv=[]
    for w in product(range(4),repeat=4):
        orbit=sorted({rotate(w,g) for g in range(8)})
        if w!=orbit[0] or not any(i in (0,2) for i in w):continue
        out=[]
        for v in orbit:
            mirror=rotate(v,7);k=min(v,mirror)
            if k not in cache:cache[k]=evaluate(data,k)
            out.append(cache[k])
        # Keep star and patch cases distinct across rootings. This stage
        # does not yet require a patch to occur at the same physical site.
        allowed=[(all(any(e[0][0]==0 for e in a[t]) for a in out),
                  all(any(e[0][0]==1 for e in a[t]) for a in out)) for t in range(2)]
        print('frame',w,'gaps',sum(i in (0,2) for i in w),'star/patch',allowed,flush=True)
        if any(any(x) for x in allowed):surv.append(w)
    print('surviving classes',len(surv),surv)
if __name__=='__main__':run()
