"""Strongest whole-fine-type overlap rows on the existing sector variables."""
from collections import defaultdict,Counter
from functools import lru_cache
from itertools import product
from .patch_square import MASKS,SYM,trans,DIR
from .square_current import states

def lift(n,ns,d,w,full=True):
    clip=lambda x:max(-w-5,min(w+5,x))
    def pos(t,i,j):
        s=n-2*t;h=d+4-t
        ax=lambda x:x if x<h else 2*h+3+x-s if x>=s-h else h+(x-h)%3
        return ax(i),ax(j),clip(i-j),clip(i+j+1-s)
    loc=[{u:pos(t,*u) for u in product(range(n-2*t),repeat=2)} for t in range(2)]
    ev=[{},{}]
    for t in (1,0):
        if not full and not t:continue
        for (i,j),k in loc[t].items():
            if k in ev[t]:continue
            s=n-2*t;img=[loc[t][trans(i,j,s,g)] for g in range(8)]
            if t:ev[t][k]=[(m,ns['p',min(zip(img,SYM[m]))]) for m in MASKS];continue
            ds=[q for q,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n];words=[]
            for f,sig in states(ds):
                nb=tuple(sig[q][int(q<2)] if q in ds else 9 for q in range(4))
                out=next((q for q,v in sig.items() if v[2]==(1 if q<2 else -1)),-1)
                kk=[]
                for g,p in enumerate(img):
                    turn=lambda h:((2-h if g&4 else h)+g)%4
                    bb=[9]*4
                    for h in range(4):bb[turn(h)]=nb[h]
                    kk.append((p,f,tuple(bb),turn(out) if out>=0 else -1))
                words.append(((f,nb,out),ns['s',min(kk)]))
            ev[t][k]=words
    ans=set()
    def link(t,u,a,b,project):
        par={};used=set()
        def rt(k):
            while k in par:k=par[k]
            return k
        for (i,j),k in loc[t].items():
            l=loc[u].get((i+a,j+b))
            if l is None:continue
            x,y=(0,k),(1,l);used.update((x,y));x,y=rt(x),rt(y)
            if x!=y:par[max(x,y)]=min(x,y)
        cs=defaultdict(Counter)
        for side,k in sorted(used):
            for e,z in ev[u if side else t][k]:
                cs[rt((side,k)),project(side,e)][z]+=1-2*side
        for c in cs.values():
            r=tuple(sorted((z,v) for z,v in c.items() if v))
            if r and r[0][1]<0:r=tuple((z,-v) for z,v in r)
            if r:ans.add(r)
    for h,(a,b) in enumerate(DIR[:2]):
        link(1,1,a,b,lambda s,m:tuple(m>>(3*(i-a*s)+j-b*s)&1 for i in range(a,3) for j in range(b,3)))
        if not full:continue
        def ss(s,e):
            f,nb,o=e;p=(h+2*s)%4;z=nb[p]
            return (f,z,int(o==p)) if not s else (z,f,int(o!=p) if f or z else 0)
        link(0,0,a,b,ss)
    if full:
        for i,j in product(range(3),repeat=2):
            dirs=[h for h,(a,b) in enumerate(DIR) if 0<=i+a<3 and 0<=j+b<3]
            link(1,0,i,j,lambda s,e:(e[0],*(e[1][h] for h in dirs)) if s else
                 (e>>(3*i+j)&1,*(e>>(3*(i+DIR[h][0])+j+DIR[h][1])&1 for h in dirs)))
    return [(r,'=') for r in sorted(ans)]
