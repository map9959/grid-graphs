"""Exact square growth after contracting the existing connected perimeter.

All old marks stay. The rest of the old forest affects the answer only
through the fact that its perimeter vertices lie in one component.
"""
from functools import lru_cache
from itertools import product
from .odd_frames import frame
import sys

@lru_cache(None)
def transitions(bits,P,neighbors,contact,keep,retain):
    # Site 0 represents the connected old perimeter.
    out=[]
    for m in (0,1):
        old=len(P);p=list(P)+[old];top=bits|m<<old
        edges=[j for j in neighbors if m or bits>>j&1]
        if contact!=-1 and (contact or m):edges.append(0)
        for j in edges:
            a,b=p[old],p[j]
            if a==b:break
            p=[b if q==a else q for q in p]
        else:
            inds=keep+(old,) if retain else keep
            roots=[p[j] for j in inds]
            out.append(((sum((top>>j&1)<<k for k,j in enumerate(inds)),tuple(roots.index(a) for a in roots)),m))
    return out

def layout(n,t,top,left):
    N=n+t;bot=t-top;right=t-left
    I=range(top,top+n);J=range(left,left+n)
    T=range(top);B=range(top+n,N);L=range(left);R=range(left+n,N)
    ji=lambda js,ii:[(i,j) for j in js for i in ii]
    ij=lambda ii,js:[(i,j) for i in ii for j in js]
    groups=[ji(J,T),ji(R,T),ij(I,R),ij(B,R),ji(reversed(J),B),ji(reversed(L),B),ij(reversed(I),L),ij(reversed(T),L)]
    assert sum(map(len,groups))==N*N-n*n
    return groups

def growth(n,t,top,left,m,trace=False,seed=None):
    groups=layout(n,t,top,left);order=sum(groups,[]);num={v:k for k,v in enumerate(order)}
    assert len(num)==len(order);live=[None];law={(0,(0,)):0}
    def near(p):
        i,j=p;return ((i+1,j),(i-1,j),(i,j+1),(i,j-1))
    last={v:max([num[v]]+[num[w] for w in near(v) if w in num]) for v in num}
    hist=[];ways={(0,(0,)):1}
    if seed is not None:
        import random
        rand=random.Random(seed)
    for k,v in enumerate(order):
        neighbors=tuple(live.index(w) for w in near(v) if w in num and num[w]<k)
        contacts=[m[i-top,j-left] for i,j in near(v) if (i-top,j-left) in m];assert len(contacts)<=1
        keep=tuple(i for i,w in enumerate(live) if i==0 or last[w]>k);retain=last[v]>k
        new={};back={};nums={}
        for (bits,P),val in law.items():
            for q,inc in transitions(bits,P,neighbors,contacts[0] if contacts else -1,keep,retain):
                if new.get(q,-1)<val+inc:
                    new[q]=val+inc
                    if trace:back[q]=((bits,P),inc)
                    if seed is not None:nums[q]=ways[bits,P]
                elif seed is not None and new[q]==val+inc:
                    nums[q]+=ways[bits,P]
                    if trace and rand.randrange(nums[q])<ways[bits,P]:back[q]=((bits,P),inc)
        law=new;ways=nums;live=[live[i] for i in keep]+([v] if retain else [])
        if trace:hist.append(back)
    val,=law.values()
    if trace:
        q=next(iter(law));selected=set()
        for p,back in reversed(list(zip(order,hist))):
            q,inc=back[q]
            if inc:selected.add(p)
        assert len(selected)==val
        return val,selected
    return (val,next(iter(ways.values()))) if seed is not None else val

def run(n,t,word):
    m=frame(n,tuple(map(int,word)));values=[]
    for a,b in product(range(t+1),repeat=2):
        q=growth(n,t,a,b,m);values.append((q,a,b))
    print(n,'padding',t,word,'maximum gain and offsets',max(values),'all gains',sorted({q for q,a,b in values}))
if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2]),sys.argv[3])
