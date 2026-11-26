"""Keep the third wing site itself when two bar holes flank a wing mark."""
from functools import lru_cache
from .sparse_spoke_tile import canon,loss

def init():
    # Both end rows have an intact backing mark and a backed neighbor.
    # The third site is blank and is identified with the root here.
    out={}
    for m in range(4):
        a,b=(1,1) if m else (1,2)
        if m&2:a=b=0
        out[m,m,canon([0,a,b,a,b,0])]=m.bit_count()
    return out

@lru_cache(None)
def transitions(old,p,backed):
    ans=[]
    for m in range(8):
        if m&(old<<1|old>>1):continue
        q=[*p,6,7,8]
        def rt(i):
            while i!=q[i]:i=q[i]
            return i
        def join(i,j):
            i,j=rt(i),rt(j);q[i]=j;return i!=j
        if any((old|m)>>i&1 and not join(3+i,6+i) for i in range(3)):continue
        if any(m>>i&3 and not join(6+i,7+i) for i in (0,1)):continue
        if (backed or m&4) and not join(0,8):continue
        ans.append((m,canon([rt(i) for i in (0,1,2,6,7,8)])))
    return ans

def step(dp,backed,a,b,prev=None):
    nd={}
    for (start,old,p),z in dp.items():
        for m,key in transitions(old,p,backed):
            score=z+b*m.bit_count()+a*int(not backed and bool(m&2))
            s=start,m,key
            if s not in nd or nd[s]<score:
                nd[s]=score
                if prev is not None:prev[s]=(start,old,p)
    return nd

def merge(*ds):
    out={}
    for d in ds:
        for s,v in d.items():out[s]=max(out.get(s,v),v)
    return out

def close(dp,a,b,buffer):
    for _ in range(buffer):dp=step(dp,True,a,b)
    out={}
    for (start,m,p),v in dp.items():
        # Last x2 mark would conflict with the preceding backing mark.
        assert m<4 and p[-1]==p[0]
        out[start,m,p[:-1]]=v
    return out

def certify(a,b,gap=2,buffer=2):
    C=step({k:b*v for k,v in init().items()},True,a,b)
    for _ in range(buffer-2):C=step(C,True,a,b)
    D=[C.copy()]+[{} for _ in range(gap-1)];seen={};peak=0
    for k in range(100):
        clean=close(C,a,b,buffer);old=close(merge(*D),a,b,buffer)
        error,example=loss(clean,old);peak=max(peak,error)
        cu=max(C.values());du=max(max(t.values(),default=0) for t in D)
        sig=lambda d,v:frozenset((k,z-v) for k,z in d.items())
        key=sig(C,cu),tuple(sig(t,du) for t in D)
        if key in seen:
            i,x,y=seen[key];drift=(du-y)-(cu-x)
            print('three-site price',a,b,'gap',gap,'excess',peak,'repeat',i,k,'relative shift',drift,flush=True)
            return peak,drift
        seen[key]=k,cu,du
        C=step(C,True,a,b)
        D=[step(merge(D[0],D[1]),True,a,b),*[step(t,True,a,b) for t in D[2:]],step(D[0],False,a,b)]
    raise AssertionError
if __name__=='__main__':
    for a,b,w in ((0,1,2),(1,2,4)):
        assert certify(a,b)==(w,0)
