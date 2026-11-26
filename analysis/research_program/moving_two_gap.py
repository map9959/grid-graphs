"""Search a 2-spacing repair in a translating strip with untouched teeth wired ahead."""
from functools import lru_cache
from fractions import Fraction as Q

@lru_cache(None)
def edges(w,old,part,shift):
    # Shift is rightward by one intact pitch group, from the bottom up.
    # The cut at either end lies between two unmarked lateral leaves.
    size=w+shift;guard=7|(7<<(w-3));forced=2|(2<<(w-3))
    if shift:
        part=(*part,0,0,0);old|=2<<w
    free=((1<<w)-1)&~guard&~(((old<<1|old>>1)>>shift))
    sub=free;out=[]
    while True:
        v=((sub|forced)<<shift)|(2 if shift else 0)
        if not v&(old<<1|old>>1):
            p=[*part,*range(size+1,2*size+1)]
            def rt(i):
                while i!=p[i]:i=p[i]
                return i
            def join(a,b):
                a,b=rt(a),rt(b);p[a]=b;return a!=b
            for i in range(size):
                j=size+1+i
                if (old|v)>>i&1 and not join(i+1,j):break
                if i and v>>(i-1)&3 and not join(j-1,j):break
            else:
                rs=[rt(0),*[rt(size+1+i) for i in range(shift,size)]]
                out.append((v>>shift,tuple(rs.index(z) for z in rs)))
        if sub==0:break
        sub=(sub-1)&free
    return out

def search(j,gap=2):
    w=3*j+gap+3;first=0,(0,)*(w+1)
    # Priming the untouched right guard with a first true row makes all
    # future incoming triples copies of an actual rooted rail group.
    st=edges(w,*first,0);D={s:s[0].bit_count()-(j+2) for s in st}
    seen={}
    for n in range(2,90):
        V={}
        for s,v in D.items():
            for sh in (0,3):
                for b,p in edges(w,*s,sh):
                    k=b,p;V[k]=max(V.get(k,-10000),v+b.bit_count()-(j+2))
        v=max(V.values());sig=frozenset((s,z-v) for s,z in V.items());D=V
        if sig in seen:
            k,z=seen[sig];print('gap',gap,'window',w,'states',len(D),'mean loss',Q(z-v,n-k),flush=True);break
        seen[sig]=n,v
    edges.cache_clear()
if __name__=='__main__':
    for j in (1,2,3):search(j)
