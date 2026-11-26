"""Exact score transfer for a 6-column sheared repeat; no SAT search."""
from functools import lru_cache
from itertools import product
from collections import Counter

class UF:
    def __init__(self,n):
        self.p=list(range(n));self.h=[0]*n;self.w=[0]*n
    def find(self,i):
        h=0
        while self.p[i]!=i:
            h+=self.h[i];i=self.p[i]
        return i,h
    def link(self,i,j,x=0):
        a,h=self.find(i);b,k=self.find(j)
        v=h+x-k
        if a==b:
            if self.w[a] or not v:return False
            self.w[a]=abs(v)
        else:
            if self.w[a] and self.w[b]:return False
            self.p[b]=a;self.h[b]=v;self.w[a]|=self.w[b]
        return True
    def load(self,s,indices):
        for i,(r,h,w) in enumerate(s):
            if i!=r and not self.link(indices[r],indices[i],h):return False
        for i,(r,h,w) in enumerate(s):
            if i==r and w and not self.link(indices[i],indices[i],w):return False
        return True
    def signature(self,indices):
        reps={};res=[]
        for i in indices:
            a,h=self.find(i);r,k=reps.setdefault(a,(len(res),h));w=self.w[a]
            res.append((r,(h-k)%w if w else h-k,w))
        return tuple(res)


def frames(top):
    best={}
    compatible={p:[m for m in range(8) if not m&((p<<1)|(p>>1))] for p in range(8)}
    def check(ms):
        uf=UF(20)
        for c,m in enumerate(ms):
            port=(c//3 if top else (c+1)//3)
            if (m&1 or c%3==(1 if top else 0)) and not uf.link(3*c,18+port%2,port//2):return
            for i in range(3):
                if i and m&(3<<(i-1)) and not uf.link(3*c+i-1,3*c+i):return
                if (ms[(c+1)%6]|m)&(1<<i) and not uf.link(3*c+i,3*((c+1)%6)+i,(c+1)//6):return
        sig=uf.signature((18,19));score=sum(m.bit_count() for m in ms)
        if sig not in best or best[sig][0]<score:best[sig]=score,ms
    def grow(ms):
        if len(ms)==6:
            if ms[0] in compatible[ms[-1]]:check(ms)
            return
        for m in (compatible[ms[-1]] if ms else range(8)):grow(ms+(m,))
    grow(())
    return best


FREE=[m for m in range(64) if not m&((m>>1)|((m&1)<<5))]

@lru_cache(maxsize=200000)
def advance(sig,old,m):
    uf=UF(12)
    assert uf.load(sig,range(6))
    for c in range(6):
        if (old|m)&(1<<c) and not uf.link(c,6+c):return
        # old (r,c) -> new (r,c-1).
        j=(c-1)%6
        if ((old>>c|m>>j)&1) and not uf.link(c,6+j,-int(c==0)):return
    return uf.signature(range(6,12))


def initial(sig):
    uf=UF(6)
    assert uf.load(sig,[1,4])
    assert uf.link(1,0) and uf.link(4,3)
    return uf.signature(range(6))


def finish(sig,bot):
    uf=UF(6)
    assert uf.load(sig,range(6))
    return uf.link(0,1) and uf.link(3,4) and uf.load(bot,(0,3))


def run(lo,hi):
    top=frames(True);bottom=frames(False)
    print("frame signature maxima",dict(Counter(v[0] for v in top.values())),
          dict(Counter(v[0] for v in bottom.values())),flush=True)
    A,B=18,9 # rods at columns 1,4 or 0,3
    # The frontier is d = physical row - column. At column c the local
    # row relative to its triple is d+(c mod 3).
    dp={(A,A,initial(s)):v for s,(v,_) in top.items()}
    prevfree=None;cert=[]
    for d in range(lo-2,hi+2):
        nd={}
        masks=[m for m in FREE if all(((m>>c)&1)==(c%3==(1 if d+c%3<lo else 0))
                                      for c in range(6) if not lo<=d+c%3<=hi)]
        for (oldold,old,sig),v in dp.items():
            for m in masks:
                if oldold&((m<<1 &63)|(m>>5)):continue
                ns=advance(sig,old,m)
                if ns is None:continue
                gain=sum((m>>c)&1 for c in range(6) if lo<=d+c%3<=hi)
                k=old,m,ns
                if v+gain>nd.get(k,-1):nd[k]=v+gain
        dp=nd
        if len(masks)==len(FREE):
            if prevfree is not None and dp=={s:q+2 for s,q in prevfree.items()}:cert.append(d)
            prevfree=dp
        print("slice",d,"states",len(dp),"best",max(dp.values()),flush=True)
    best=max(v+w for (_,m,s),v in dp.items() if m==B
             for bot,(w,_) in bottom.items() if finish(s,bot))
    net=best-2*(hi-lo+1)
    print("width 6 rows",lo,hi,"selected",best,"debit",2*(hi-lo+1),"exact net",net)
    print("full-vector +2 shifts at free slices:",cert)
    if hi-lo+1>=15:
        assert cert and net==15
    return net

if __name__=="__main__":
    import sys
    run(*(int(s) for s in sys.argv[1:]))
