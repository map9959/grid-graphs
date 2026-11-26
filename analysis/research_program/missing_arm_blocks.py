"""Rooted overlap of a missing-arm block and both of its neighbors."""
from collections import defaultdict
from functools import lru_cache
from itertools import product
from .arm_budget_bands import advance,cols
from .western_cut_transfer import BT,north_star_union,typ

@lru_cache(None)
def hop(a,b,c,d):
    # Distance-one or -two mark pair straddling the transverse cut in a
    # square of four tiles. Every such pair lies in some complete plaquette.
    side=lambda u,v:{(i,3*j+l) for j,m in enumerate((u,v)) for i,l in product(range(3),repeat=2)
                     if m>>(3*i+l)&1}
    return any(3+x-i+abs(y-j)<=2 for i,j in side(a,b) for x,y in side(c,d))

def transfer(axis,H=4,closed=True,pump=False,limit=32,free_length=False,stars=False,priced=None,all_missing=False,trace=False,clean=(),outer_closed=False,rim=False,outer_sides=3,cross_both=False,pump_mask=None):
    # Two cuts, after the first and before the last tile column. The graph
    # on the entire width sees every forced join across both cuts.
    # Optionally test whether all marked components of the central block
    # already have their perimeter root before either side is attached.
    K=38
    @lru_cache(None)
    def by(v,eligible):
        tab=defaultdict(list);out=defaultdict(list)
        for a,b,c,d in (north_star_union() if stars else BT)[6,v]:
            if any(e and m&16 and m&(130 if axis==1 else 40)
                   for e,m in zip(eligible*2,(a,b,c,d))):continue
            tab[a,b].append((c,d))
        def grow(w,y):
            if len(w)==H:out[w].append(y);return
            for a,b in tab[w[-1],y[-1]]:
                if len(w) in clean and hop(w[-1],y[-1],a,b):continue
                grow((*w,a),(*y,b))
        for a,b in list(tab):grow((a,),(b,))
        return out
    def links(j):return by(typ(j,K),tuple(min(x,K-x)>=4 for x in (j,j+1)))
    @lru_cache(maxsize=150000)
    def step(z,w,end,cutmask):
        n=len(w)*3
        for l,m in enumerate(cols(w)):
            z=advance(z,m,(1<<n)-1 if end and l==1 else 0,cutmask)
            if z is None:break
        return z
    def base(h):return -1,tuple(range(3*h+1)),(0,)*(3*h)+(1,)
    def move(z,w,j):
        a,b=z;end=j in (0,K)
        if closed:
            b=step(b,w[1:-1],end,0)
            if b is None or (j==K and 2 in b[2]):return
        cuts=(outer_sides&1)|((outer_sides>>1)<<(3*H-1))
        a=step(a,w,end,0 if outer_closed else cuts)
        if a is None or (j==K and 2 in a[2]):return
        return a,b
    @lru_cache(None)
    def loss(w):return 3*H-sum(x.bit_count() for x in w) if priced is None else 3-w[priced].bit_count()
    def missing(w,j):
        x=6 if j==0 else 7 if j<13 else 192 if j==K else 448 if j>K-12 else None
        return sum((x is not None and m!=x)<<i for i,m in enumerate(w if all_missing else w[1:-1]))
    @lru_cache(None)
    def joins(w,y):
        if not cross_both:return 0
        return sum(hop(w[i],y[i],w[i+1],y[i+1])<<(H+b) for b,i in enumerate((0,H-2)))
    mask=(1<<(limit+1))-1 if limit is not None else None
    st={};init=base(H),base(H-2) if closed else ()
    if rim:
        from .missing_arm_rim import words
        north,south=words(H,True,rim if rim in (-4,4) else None),words(H,False)
    for w in links(0):
        if rim and w not in north:continue
        z=move(init,w,0)
        if z is not None:st[w,z,missing(w,0)]=1 if mask is None else 1<<loss(w)
    def next_layer(j,src):
        nd={};tab=links(j)
        for (w,z,miss),b in src.items():
            if j==18 and pump and (loss(w) or w not in tab[w] or move(z,w,j)!=z):continue
            if j==18 and pump_mask is not None and w!=(pump_mask,)*H:continue
            for y in tab[w]:
                if rim and j==K-1 and y not in south:continue
                v=1 if mask is None else (b<<loss(y))&mask
                if not v:continue
                t=move(z,y,j+1)
                if t is not None:
                    key=y,t,miss|missing(y,j+1)|joins(w,y);nd[key]=nd.get(key,0)|v
        return nd
    history=[]
    for j in range(K):
        if trace:history.append(st)
        st=next_layer(j,st)
        if j==18 and free_length:
            new=st
            while new:
                delta={}
                for key,b in next_layer(j,new).items():
                    d=b&~st.get(key,0)
                    if d:delta[key]=d;st[key]=st.get(key,0)|d
                new=delta
    ans=defaultdict(int) if all_missing else [0]*(H-1)
    for (_,_,miss),b in st.items():
        if cross_both and miss>>H!=3:continue
        miss&=(1<<H)-1
        ans[miss if all_missing else miss.bit_count()]|=b
    if not trace:return ans
    assert pump and not free_length and priced is None
    def path(c):
        target=(1<<(H if all_missing else H-2))-1
        key=next(key for key,b in st.items() if b>>c&1 and key[-1]==(target|(3<<H if cross_both else 0)))
        path=[key[0]]
        for j in reversed(range(K)):
            y,t,miss=key;c-=loss(y);byj=links(j)
            key=next((w,z,d) for (w,z,d),b in history[j].items() if b>>c&1 and
                     (d|missing(y,j+1)|joins(w,y))==miss and y in byj[w] and move(z,y,j+1)==t and
                     (j!=18 or ((pump_mask is None or w==(pump_mask,)*H) and not loss(w) and w in byj[w] and move(z,w,j)==z)))
            path.append(key[0])
        assert c==loss(path[-1]);return path[::-1]
    return ans,path

if __name__=='__main__':
    import sys
    a,h,closed=map(int,sys.argv[1:4])
    b=transfer(a,h,closed,'--pump' in sys.argv,free_length='--all' in sys.argv,stars='--stars' in sys.argv)
    print(a,h,closed,'minimum by missing count',[(v&-v).bit_length()-1 for v in b])
