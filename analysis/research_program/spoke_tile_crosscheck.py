"""Exhaust the physical four-column rectangles, without contracting their side rail."""
from itertools import product
from .sparse_spoke_tile import canon,layer
from . import alternating_spoke_tile as alt

def check(H,holes,wide=False):
    n=4*H;pairs=[(i,k) for i in range(n) for k in (i+1,i+4)
                  if k<n and (k==i+4 or i%4!=3)]
    tab={}
    words=[range(8 if wide and y-1 in holes and y+1 in holes else 4) for y in range(H)]
    count=0
    for word in product(*words):
        count+=1
        bits=sum((v|(8 if y not in holes else 0))<<(4*y) for y,v in enumerate(word))
        par=list(range(n))
        def rt(i):
            while par[i]!=i:i=par[i]
            return i
        for i,k in pairs:
            if not (bits>>i|bits>>k)&1:continue
            a,b=rt(i),rt(k)
            if a==b:break
            par[a]=b
        else:
            key=word[0],word[-1],canon([rt(i) for i in (3,0,1,n-4,n-3)])
            score=sum(v.bit_count() for v in word)
            tab[key]=max(tab.get(key,0),score)
    if wide:
        dp=alt.init()
        for y in range(1,H):dp=alt.step(dp,y not in holes,0,1)
        assert tab=={(a,b,p[:-1]):v for (a,b,p),v in dp.items()}
    else:assert tab==layer(H,holes)
    print('physical wing words',count,'holes',sorted(holes),'end partition prices matched',len(tab))

if __name__=='__main__':
    for h,z in ((5,set()),(5,{2}),(7,{2,4}),(8,{2,5})):check(h,z)
    check(7,{2,4},True)
