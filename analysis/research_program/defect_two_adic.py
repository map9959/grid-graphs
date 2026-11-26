"""Prime-power lattice obstruction for a single charged occurrence."""
from .odd_charge_parity import build,possible,Counter
import sys

def add(a,b):
    out=[];c=0
    for x,y in zip(a,b):
        v=x^y;out.append(v^c);c=(x&y)|(v&c)
    return tuple(out)

class Module:
    def __init__(self,cols,d):
        self.piv={};even=[]
        for a in cols:
            while a[0]:
                h=a[0].bit_length()-1;b=self.piv.get(h)
                if b is None:self.piv[h]=a;break
                a=add(a,b)
            else:
                if any(a[1:]):even.append(a[1:])
        if d>1:
            # A mod-two relation is either one of the dependent-column
            # reductions or twice a pivot. Divide these generators by two.
            even.extend(b[:-1] for b in self.piv.values())
            self.next=Module(even,d-1)
        else:self.next=None
    def contains(self,a):
        while a[0]:
            b=self.piv.get(a[0].bit_length()-1)
            if b is None:return False
            a=add(a,b)
        return self.next.contains(a[1:]) if self.next else True

def run(d):
    cols,qs,_,_,lab,rd,mass=build(35);take=possible(cols,qs,rd,mass,lab,(72,))
    if '--dimers' in sys.argv:
        from .charge_dimers import extend
        extend(35,cols,qs,rd,mass,lab,take)
        for i,ok in enumerate(take):
            if not ok:qs[i]=73
        take=possible(cols,qs,rd,mass,lab,(72,))
    def bits(count):
        b=[0]*d
        for i,w in count.items():
            for j in range(d):
                if w>>j&1:b[j]|=1<<i
        return tuple(b)
    def col(a,sgn):
        count=Counter()
        for r in a:count[r if r>=0 else ~r]+=sgn if r>=0 else -sgn
        return bits(count)
    module=Module((col(a,1) for a,q,ok in zip(cols,qs,take) if ok and not q),d)
    defects=[(e,col(a,-1)) for e,a,q,ok in zip(lab,cols,qs,take) if ok and q]
    for t in range(1<<d):
        n=35+42*t;k=(n-2)//3;counts={rd['score',]:3*k*k+7*k-(k-5)//7}
        for key in mass:
            tag,i,j=key;h=6-tag
            size=lambda z:(n-2*tag-2*h+5-(z-h))//6 if h<=z<h+6 else 1
            counts[rd['norm',key]]=size(i)*size(j)
        b=bits(counts);good=[e for e,a in defects if module.contains(add(b,a))]
        print('t',t,'mod',1<<d,'single-defect survivors',len(good),Counter(k[0] for k,e in good),flush=True)
if __name__=='__main__':run(int(sys.argv[1]))
