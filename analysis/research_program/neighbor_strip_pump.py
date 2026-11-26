"""Find replayable, constant-deficit coupled horizontal strip fillings."""
import gzip,json,sys
from functools import lru_cache
from itertools import product
from pathlib import Path
from .tile_family_lp import typ

@lru_cache(None)
def advance(z,m,teeth):
    old,part=z;h=len(part)-1;p=list(part)+list(range(h+1,2*h+1))
    def root(x):
        while p[x]!=x:x=p[x]
        return x
    def edge(x,y):
        a,b=root(x),root(y);p[a]=b;return a!=b
    for i in range(h):
        if old>=0 and (old|m)>>i&1 and not edge(i,h+1+i):return
        if i and m>>(i-1)&3 and not edge(h+i,h+i+1):return
        if (m&teeth)>>i&1 and not edge(h+1+i,h):return
    ids={}
    # Use indices in the next frontier, not the old union-find array.
    return m,tuple(ids.setdefault(root(x),i) for i,x in enumerate((*range(h+1,2*h+1),h)))

@lru_cache(None)
def cols(w):
    return tuple(sum((m>>(3*a+j)&1)<<(3*i+a) for i,m in enumerate(w)
                     for a in range(3)) for j in range(3))

def run(r,H,axis):
    k=39;K=k-1
    B={(u,v):words for u,v,words in json.loads(gzip.decompress(
        Path('target/tile_family_3_5_h6.json.gz').read_bytes()))}
    @lru_cache(None)
    def words(j):
        tabs=[]
        for i in range(r,r+H-1):
            tab={}
            for a,b,c,d in B[typ(i,K),typ(j,K)]:
                if any(min(i+di,j+dj,k-1-i-di,k-1-j-dj)>=4 and m&16 and m&(40 if axis==1 else 130)
                       for (di,dj),m in zip(product(range(2),repeat=2),(a,b,c,d))):continue
                tab.setdefault((a,b),[]).append((c,d))
            tabs.append(tab)
        pairs={}
        def grow(w,y):
            if len(w)==H:pairs.setdefault(w,[]).append(y);return
            for a,b in tabs[len(w)-1].get((w[-1],y[-1]),()):grow((*w,a),(*y,b))
        for a,b in tabs[0]:grow((a,),(b,))
        return pairs
    rim=(1<<(3*H-2)) if r+H==k else 0
    def step(z,w,j):
        for l,m in enumerate(cols(w)):
            z=advance(z,m,(1<<(3*H))-1 if l==1 and j in (0,k-1) else rim)
            if z is None:break
        return z
    def loss(w):return 3*H-sum(m.bit_count() for m in w)
    st={}
    for w in words(0):
        z=step((-1,tuple(range(3*H+1))),w,0)
        if z is not None:st[w,z]=loss(w),(w,)
    for j in range(K):
        by=words(j if j<6 or j>=K-6 else 6);nd={}
        for (w,z),(d,path) in st.items():
            if j==12 and (loss(w) or w not in by.get(w,()) or step(z,w,j)!=z):continue
            for y in by.get(w,()):
                s=step(z,y,j+1)
                if s is not None:
                    key=y,s;v=d+loss(y)
                    if key not in nd or v<nd[key][0]:nd[key]=v,(*path,y)
        st=nd
    if not st:print('no constant-column pump found',r,H,axis);return
    d,path=min(st.values());print(r,H,axis,'constant total deficit',d,'pump',path[12])
    return path

if __name__=='__main__':run(*map(int,sys.argv[1:]))
