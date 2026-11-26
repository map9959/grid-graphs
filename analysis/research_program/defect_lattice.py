"""Exact bit-sliced GF(3)/GF(7) quotient for the single remaining defect."""
from .odd_charge_parity import build,possible
from collections import Counter
import sys

def run(p):
    k={3:2,7:3}[p];zero=(0,)*k
    def plus(a,b):
        out=[];carry=0
        for x,y in zip(a,b):
            v=x^y;out.append(v^carry);carry=(x&y)|(v&carry)
        for i in range(k):
            z=out[i];out[i]=z^carry;carry &= z
        assert not carry
        m=out[0]&out[1]
        if k==3:m&=out[2]
        return tuple(a^m for a in out)
    def scalar(a,s):
        if s==1:return a
        if s==0:return zero
        if s in (p-1,p-2) or (p==7 and s==3):
            mask=0
            for x in a:mask|=x
            a=tuple(x^mask for x in a);s=p-s
        sh=s.bit_length()-1;return a[-sh:]+a[:-sh] if sh else a
    def make(cs):
        out=[0]*k
        for i,w in cs.items():
            for j in range(k):
                if (w%p)>>j&1:out[j]|=1<<i
        return tuple(out)
    n=35;cols,qs,_,_,labels,rd,mass=build(n);take=possible(cols,qs,rd,mass,labels,(72,))
    if '--dimers' in sys.argv:
        from .charge_dimers import extend
        extend(n,cols,qs,rd,mass,labels,take)
        for i,z in enumerate(take):
            if not z:qs[i]=73
        take=possible(cols,qs,rd,mass,labels,(72,))
    piv={}
    def reduce(a,insert):
        r=list(zero)
        while any(a):
            i=max(x.bit_length() for x in a)-1;v=sum((x>>i&1)<<j for j,x in enumerate(a));u=piv.get(i)
            if u is None:
                if insert:
                    piv[i]=scalar(a,pow(v,-1,p));return
                z=1<<i
                for j in range(k):
                    if v>>j&1:r[j]|=z
                a=tuple(x&~z for x in a);continue
            a=plus(a,scalar(u,p-v))
        return tuple(r)
    def column(cs):
        ct=Counter()
        for r in cs:ct[r if r>=0 else ~r]+=1 if r>=0 else -1
        return make(ct)
    for q,cs,ok in zip(qs,cols,take):
        if not q and ok:reduce(column(cs),True)
    defects=[(e,reduce(column(cs),False)) for e,q,cs,ok in zip(labels,qs,cols,take) if ok and q==72]
    d0=int(next((s[2:] for s in sys.argv if s.startswith('d=')),6))
    for t in range(p):
        N=35+42*t;h=(N-2)//3;rhs={rd['score',]:3*h*h+7*h-(h-5)//7}
        for (tag,i,j) in mass:
            d=d0-tag
            def ct(z):return (N-2*tag-2*d+5-(z-d))//6 if d<=z<d+6 else 1
            rhs[rd['norm',(tag,i,j)]]=ct(i)*ct(j)
        z=reduce(make(rhs),False);valid=[e for e,y in defects if z==y]
        print('p',p,'t mod p',t,'zero rank',len(piv),'single defect survivors',len(valid),
              Counter(k[0] for k,e in valid),flush=True)
if __name__=='__main__':run(int(sys.argv[1]))
