"""Simultaneous west/east contacts of the one-unrooted-component fan."""
from functools import lru_cache
from collections import defaultdict
from .arm_budget_bands import transpose,typ,B
from .missing_arm_budget_audit import fan_word

@lru_cache(None)
def tables(v,left):
    tab=defaultdict(lambda:defaultdict(list))
    for w in B[v,6]:
        a,b,c,d=(transpose(w[q]) for q in (0,2,1,3))
        fixed,new=((c,d),(a,b)) if left else ((a,b),(c,d))
        tab[fixed][new[0]].append(new[1])
    return tab

@lru_cache(None)
def advance(state,m,teeth,contacts,e):
    # Frontier of three sites, the perimeter root (index 3), and the
    # single unrooted tree in the old block (index 4).
    old,pp,flags=state;p=list(pp)+[5,6,7];tags=list(flags)+[m>>i&1 for i in range(3)]
    def root(x):
        while p[x]!=x:x=p[x]
        return x
    def edge(a,b):
        a,b=root(a),root(b)
        if a==b:return False
        p[a]=b;tags[b]|=tags[a];return True
    for i in range(3):
        if old>=0 and (old|m)>>i&1 and not edge(i,5+i):return
        if i and m>>(i-1)&3 and not edge(4+i,5+i):return
        if teeth and m>>i&1 and not edge(5+i,3):return
    if contacts>=0 and not edge(5+e,contacts):return
    roots=[root(i) for i in (5,6,7,3,4)]
    if any(tags[x] and p[x]==x and x not in roots for x in range(3)):return
    ids={};part=tuple(ids.setdefault(v,i) for i,v in enumerate(roots))
    return m,part,tuple(tags[v] if i==part[i] else 0 for i,v in enumerate(roots))

def cap(k,H,left,axis,free=False):
    x=0 if left else H-1;M=k-2;K=k-1
    w=fan_word(k,x,M)
    n=3*k;e=2 if left else 0
    masks=[sum((v>>(3*l+b)&1)<<(3*j+b) for j,v in enumerate(w) for b in range(3)) for l in range(3)]
    old=masks[2-e];live=old|(old>>1)|(old<<1)|masks[1]
    def step(z,y,j):
        if min(j,K-j)>=4 and y&16 and y&(130 if axis==1 else 40):return
        for l in range(3):
            m=sum((y>>(3*i+l)&1)<<i for i in range(3));q=3*j+l
            c=-1
            if live>>q&1 and ((old>>q&1) or m>>e&1):
                c=3 if left and q<=3 else 4
            z=advance(z,m,l==1 and j in (0,K),c,e)
            if z is None:break
        return z
    def tab(j):return tables(typ(j,K),left)[tuple(w[j:j+2])]
    def move(src,j):
        out={};t=tab(j)
        for (m,z),bits in src.items():
            for y in t[m]:
                s=step(z,y,j+1)
                if s is not None:out[y,s]=out.get((y,s),0)|(1 if free else bits<<(3-y.bit_count()))
        return out
    base=-1,tuple(range(5)),(0,0,0,0,1);st={}
    for m in tab(0):
        z=step(base,m,0)
        if z is not None:st[m,z]=1 if free else 1<<(3-m.bit_count())
    repeats=set()
    for j in range(K):
        st=move(st,j)
        if free and 7<=j<K-7 and w[j]==w[j+1] and w[j] not in repeats:
            repeats.add(w[j]);new=st
            while new:
                more=move(new,j);new={key:1 for key in more if key not in st};st.update(new)
    ans=[0,0]
    for (_,(_,p,f)),b in st.items():
        if all(not val or i in (p[3],p[4]) for i,val in enumerate(f)):ans[int(p[3]==p[4])]|=b
    return ans,repeats
def check():
    # West is fixed at p=1. To the east p>=4, with three possible
    # switch phases; from p=9 on, the 7 and 56 runs can both be pumped.
    assert cap(39,12,True,1,True)==([1,0],{56})
    for H in range(12,28):
        (unattached,rooted),repeat=cap(39,H,False,1,True)
        assert unattached and not rooted and 56 in repeat
        if H>=25:assert 7 in repeat
    print('fan side transfer: U can stay open; neither one-column cap can root U (all lengths)')
if __name__=='__main__':check()
