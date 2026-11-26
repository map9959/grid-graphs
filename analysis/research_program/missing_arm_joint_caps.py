"""Successive caps of the missing-arm fan with its spanning tree U kept live."""
from collections import defaultdict
from functools import lru_cache
from .missing_arm_contacts import tables
from .missing_arm_budget_audit import fan_word
from .neighbor_strip_pump import cols
from .tile_family_lp import typ

@lru_cache(maxsize=90000)
def put(z,m,teeth,contact,near):
    old,part,data=z;h=len(part)-2;p=list(part)+list(range(h+2,2*h+2))
    f=list(data)+[(m>>i)&1 for i in range(h)]
    def rt(i):
        while p[i]!=i:i=p[i]
        return i
    def edge(i,j):
        a,b=rt(i),rt(j)
        if a==b:return False
        p[a]=b;f[b]|=f[a];return True
    for i in range(h):
        a=h+2+i
        if old>=0 and (old|m)>>i&1 and not edge(i,a):return
        if i and m>>(i-1)&3 and not edge(a-1,a):return
        if teeth and m>>i&1 and not edge(a,h):return
    if contact>=0 and not edge(h+2+near,h+contact):return
    roots=[rt(i) for i in (*range(h+2,2*h+2),h,h+1)]
    if any(f[i] and p[i]==i and i not in roots for i in range(h)):return
    ids={};part=tuple(ids.setdefault(v,i) for i,v in enumerate(roots))
    return m,part,tuple(f[v] if i==part[i] else 0 for i,v in enumerate(roots))

def costs(k,H,left,h,free=False):
    """All h new columns in the bulk chart, scanned together, no intermediate rooting."""
    K=k-1;x=0 if left else H-1;w=fan_word(k,x,k-2)
    n=3*k;h3=3*h;near=h3-1 if left else 0
    col=[sum((v>>(3*l+b)&1)<<(3*j+b) for j,v in enumerate(w) for b in range(3)) for l in range(3)]
    old=col[0 if left else 2];live=old|(old<<1)|(old>>1)|col[1]
    @lru_cache(None)
    def links(v,jj,a,b):
        t=tables(v,left);out=defaultdict(list)
        def grow(y,z):
            if len(y)>h:
                out[y[1:]].append(z[1:]);return
            for c,ds in t[y[-1],z[-1]].items():
                for d in ds:
                    if any(min(j,K-j)>=4 and m&16 and m&130 for j,m in ((jj,c),(jj+1,d))):continue
                    grow(y+(c,),z+(d,))
        grow((a,),(b,));return out
    def tab(j):return links(typ(j,K),j if not 6<=j<K-6 else 6,w[j],w[j+1])
    def advance(z,y,j):
        for l,m in enumerate(cols(y[::-1] if left else y)):
            q=3*j+l;c=-1
            if live>>q&1 and (old>>q&1 or m>>near&1):c=0 if left and q<=3 else 1
            z=put(z,m,l==1 and j in (0,K),c,near)
            if z is None:break
        return z
    def loss(y):return h3-sum(m.bit_count() for m in y)
    base=-1,tuple(range(h3+2)),(0,)*(h3+1)+(1,);st={}
    for y in tab(0):
        z=advance(base,y,0)
        if z is not None:st[y,z]=1 if free else 1<<loss(y)
    def move(src,j):
        nd={};t=tab(j)
        for (y,z),bits in src.items():
            for v in t[y]:
                a=advance(z,v,j+1)
                if a is not None:nd[v,a]=nd.get((v,a),0)|(1 if free else bits<<loss(v))
        return nd
    repeats=set()
    for j in range(K):
        st=move(st,j)
        if free and 7<=j<K-7 and w[j]==w[j+1] and w[j] not in repeats:
            repeats.add(w[j]);extra=st
            while extra:
                more=move(extra,j);extra={key:1 for key in more if key not in st};st.update(extra)
    ans=[0,0]
    for (_,(_,p,f)),bits in st.items():
        if all(not v or i in (p[h3],p[h3+1]) for i,v in enumerate(f)):ans[int(p[h3]==p[h3+1])]|=bits
    return ans

def check():
    from .western_cut_transfer import BT
    interior={(48,56),(56,56),(56,24)}
    for v in range(13):
        to_east={(c,d) for a,b,c,d in BT[v,6] if a==b==56}
        to_west={(a,b) for a,b,c,d in BT[v,6] if c==d==56}
        assert to_east==to_west==(interior if 3<=v<=9 else set())
    print('56 run loses at most two tiles per transverse step; forbidden at fringe types 2 and 10')
    for h in (2,3,4):
        # The eastern boundary of the fan has p=4,...,8 or p>=9.
        # The small cases have only a free 56 run; from p=9 the inner
        # 7 and 56 runs can be lengthened independently.
        for H in range(12,28):
            assert costs(39,H,False,h,True)==[1,0]
        assert costs(39,12,True,h,True)==[1,0]
        a,b=(costs(39,12,L,h) for L in (True,False))
        assert all((x&-x).bit_length()-1==3*h and y==0 for x,y in (a,b))
        print('width',h,'on both cuts: open costs start at',3*h,
              'each; exactly-one-root joint cost set is empty at all lengths')
if __name__=='__main__':check()
