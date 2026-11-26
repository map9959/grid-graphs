"""Independent small physical cap enumeration (no contracted or weighted graph input)."""
from itertools import product
from .joint_frame_caps import cap

def audit(n,h,L,R):
    # Free rows and one wing row; the pitch triples in the last
    # row are actual physical trees. Remove only their two fixed marks
    # from the objective, as the interior ledger counts them.
    prices={k:{} for k in product((0,1),repeat=2)}
    hn=h*n;end=n-1-R
    lower=[*range(L-1),*range(end+2,n)]
    teeth=range(hn+L,hn+end+1,3);sites=hn+n
    pairs=[(i,j) for i in range(sites) for j in (i+1,i+n)
           if j<sites and (j==i+n or i%n!=n-1)]
    for m in range(1<<(hn+len(lower))):
        mask=(m% (1<<hn))|sum(1<<x for x in teeth)
        for i,x in enumerate(lower):mask|=(m>>(hn+i)&1)<<(hn+x)
        p=list(range(sites))
        def rt(i):
            while p[i]!=i:i=p[i]
            return i
        for i,j in pairs:
            if not (mask>>i|mask>>j)&1:continue
            u,v=rt(i),rt(j)
            if u==v:break
            p[u]=v
        else:
            for k,tab in prices.items():
                labels={rt(x) for x in teeth}
                for bit,x in zip(k,(hn,sites-1)):
                    if bit:labels.add(rt(x))
                    elif mask>>x&1:break
                else:
                    c=len(labels);j=min(c,2)
                    tab[j]=max(tab.get(j,0),10*(mask.bit_count()-len(teeth))+7*c)
    for k,raw in prices.items():
        v,_=cap(n,h,L,R,1,range(L,end+1,3),links=k)
        assert v==raw
        print('physical joint cap',k,raw)

if __name__=='__main__':
    audit(10,1,3,3);audit(8,2,2,2)
