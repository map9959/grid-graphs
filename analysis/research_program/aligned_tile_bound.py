"""Mark counts in the disjoint aligned 3x3 tiles of a one-gap target."""
from itertools import product
from collections import Counter
from .defect_window import table,DIR

def check(n):
    T,P,S=table(n);k=(n-2)//3;assert n%42==35 and k>=39
    dep=lambda i,j:min(i,j,n-1-i,n-1-j)
    hist=Counter();types={}
    for i,j in product(range(1,n-1,3),repeat=2):
        tile=[(i+a,j+b) for a,b in product(range(3),repeat=2)]
        empty=sum(1<<s for s,p in enumerate(tile) if dep(*p)==1)
        forbidden=[]
        for t in range(3):
            for d,(a,b) in enumerate(DIR[:2]):
                x,y=(i+t,j) if d==0 else (i,j+t)
                z,w=x+2*a,y+2*b
                if min(dep(x,y),dep(z,w))<2:continue
                pref=lambda u,v,e:dep(u,v)>2 and S(T(0,u,v),(0,1,2,3),e,False,False)[1]==0
                if not (pref(x,y,d) or pref(z,w,d+2)):
                    ends=(1<<(3*(x-i)+y-j))|(1<<(3*(z-i)+w-j))
                    mid=1<<(3*(x+a-i)+y+b-j);forbidden.append((ends,mid))
        may_isolate=(i==1 or j==1) and 5<=max(i,j)+1<=n-6
        key=(T(1,i,j),empty,tuple(forbidden),may_isolate)
        if key not in types:
            counts={m.bit_count() for m,q in enumerate(P(key[0])) if q==0 and not m&empty and
                    (m&186 or may_isolate) and all(m&e!=e or m&mid for e,mid in forbidden)}
            assert min(counts)>=1 and max(counts)<=3
            types[key]=max(counts)
        hist[types[key]]+=1
    assert hist=={2:4,3:k*k-4}
    U=3*k*k+7*k-(k-5)//7
    print(n,k*k,'disjoint tiles, at least one mark each, maxima',dict(hist),'target deficit',3*k*k+4*n-9-U)
if __name__=='__main__':
    check(119);check(203)
