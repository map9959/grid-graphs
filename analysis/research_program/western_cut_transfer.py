"""Continue a fully rooted east frontier westward, without resetting its roots."""
from collections import defaultdict
from functools import lru_cache
from .arm_budget_bands import advance,B,transpose,spectrum,K,typ,physical
from .joined_arm_budget import layout,west,certify_groups,row

BT={(v,u):{tuple(transpose(w[h]) for h in (0,2,1,3)) for w in ws}
    for (u,v),ws in B.items()}

@lru_cache(None)
def north_star_union():
    from pathlib import Path
    from hashlib import sha256
    import gzip,json
    out=dict(BT)
    for j in range(3):
        out[6,j]=set(BT[6,j])
        for ph in range(-5,11,3):
            p=Path('target/tile_star_catalogues')/f'word_{j}_6_{ph}'
            raw=p.with_suffix('.json.gz').read_bytes()
            a,b,_,digest=p.with_suffix('.check').read_text().split()
            assert (a,b,digest)==('s','VERIFIED',sha256(raw).hexdigest())
            out[6,j].update(tuple(transpose(w[l]) for l in (0,2,1,3))
                            for w in json.loads(gzip.decompress(raw)))
    return out

def lanes(w):
    return [sum((v>>(3*l+b)&1)<<(3*j+b) for j,v in enumerate(w) for b in range(3))
            for l in range(3)]

def rooted_front(w):
    # Every processed marked component has one tooth. Precisely the
    # exposed sites with an incident processed edge belong to a rooted
    # component; all others are unmarked singleton frontier classes.
    m,inner,_=lanes(w);n=3*len(w)
    live=m|(m<<1)|(m>>1)|inner
    r=next((i for i in range(n) if live>>i&1),n)
    pp=tuple(r if live>>i&1 else i for i in range(n))+(r,)
    return m,pp,tuple(3 if i==r else 0 for i in range(n+1))

@lru_cache(None)
def choices(axis,old):
    k=len(old);by=[]
    for j in range(k-1):
        d=defaultdict(list)
        for a,b,c,e in BT[6,typ(j,k-1)]:
            if (c,e)!=old[j:j+2]:continue
            if any(min(x,k-1-x)>=4 and m&16 and m&(130 if axis==1 else 40)
                   for x,m in ((j,a),(j+1,b))):continue
            d[a].append(b)
        by.append(d)
    def walk(w):
        j=len(w)-1
        if j==k-1:yield tuple(w);return
        for m in by[j][w[-1]]:yield from walk(w+[m])
    return tuple(y for m in by[0] for y in walk([m]))

def traverse(axis,w,front):
    n=3*len(w);st={(w,front):1};hist=[]
    while st:
        hist.append(len(st));out={}
        for (old,z),costs in st.items():
            for y in choices(axis,old):
                f=z
                for m in reversed(lanes(y)):
                    f=advance(f,m,2|(1<<(n-2)),0)
                    if f is None:break
                if f is None:continue
                bits=costs<<sum(3-m.bit_count() for m in y)
                if bits:out[y,f]=out.get((y,f),0)|bits
        st=out
        if len(hist)>100:raise RuntimeError('long continuation')
    return hist

def coupled(axis,s,h,inner=4,outer_roots=False,trace=False,break_from=None,middle=None,long_prefix=False,
            all_stars=False,repeat_middle=False):
    """Cost set on h new columns; innermost `inner` must already be rooted.

    Both automata see the same marks. The larger automaton alone allows
    escapes at its far western cut. The previous diagonal at the east
    is represented by its actual rooted contacts and unique attachment.
    """
    k=39;boundary=([6]+[7]*(s-1)+list(middle if middle is not None else (16,16))+[448]*k)[:k-1]+[192]
    @lru_cache(None)
    def links(v,jj,c,d):
        # Build outwards from the fixed cut, not via a Cartesian product
        # of independent band witnesses.
        by=defaultdict(list);out=defaultdict(list)
        for a,b,x,y in (north_star_union() if all_stars else BT)[6,v]:
            if any(min(jj+i,K-jj-i)>=4 and m&16 and m&(130 if axis==1 else 40)
                   for i,m in ((0,a),(1,b),(0,x),(1,y))):continue
            by[x,y].append((a,b))
        def grow(w,y):
            if len(w)==h+1:out[w[1:]].append(y[1:]);return
            for a,b in by[w[-1],y[-1]]:grow(w+(a,),y+(b,))
        grow((c,),(d,));return out
    def transitions(j):return links(typ(j,K),j if j<6 or j>=K-6 else 6,boundary[j],boundary[j+1])
    def init(n):return -1,tuple(range(3*n+1)),(0,)*(3*n)+(1,)
    from .neighbor_strip_pump import cols
    @lru_cache(maxsize=150000)
    def step(z,y,end,mroot,need,strict):
        n=3*len(y)
        # Reverse into west-to-east order: easternmost physical lane last.
        for l,m in enumerate(cols(y[::-1])):
            if need>>l&1 and not m>>(n-1):return
            contact=bool(mroot>>(l+3)&1 or (mroot>>l&1 and m>>(n-1)))
            cuts=(0 if strict else 1)|((1<<(n-1)) if middle is not None else 0)
            z=advance(z,m,(1<<n)-1 if end and l==1 else 0,cuts,contact)
            if z is None:break
        return z
    def move(z,y,j,strict):
        rooted=sum((3*j+b<3*s+(2 if middle is None else 1))<<b for b in range(3))
        mroot=rooted|((rooted & boundary[j])<<3)
        need=2 if middle is None and j==s+1 else 0
        return step(z,y,j in (0,K),mroot,need,strict)
    def pair(zz,w,j):
        v=zz[1]
        if inner:
            v=move(v,w[:inner],j,True)
            if v is None or j==K and 2 in v[2]:return
        u=move(zz[0],w,j,outer_roots)
        if u is not None and (j!=K or 2 not in u[2]):return u,v
    def cost(w):return 3*len(w)-sum(v.bit_count() for v in w)
    st={};base=init(h),init(inner) if inner else ();history=[]
    for w in transitions(0):
        zz=pair(base,w,0)
        if zz is not None:st[w,zz,False]=1<<cost(w)
    def next_layer(src,j):
        by=transitions(j);nd={}
        for (w,zz,diff),bits in src.items():
            for y in by[w]:
                z=pair(zz,y,j+1)
                if z is not None:
                    key=y,z,diff or (break_from is not None and break_from<=j+1<K and y[-1]!=448)
                    nd[key]=1 if long_prefix else nd.get(key,0)|(bits<<cost(y))
        return nd
    for j in range(K):
        if trace:history.append(st)
        st=next_layer(st,j)
        if long_prefix and j==7 or repeat_middle and j==s+1:
            assert not trace and (break_from is None or break_from>8)
            if j!=7:assert long_prefix and boundary[j:j+2]==[56,56] and break_from is None
            extra=st
            while extra:
                nd=next_layer(extra,j)
                extra={key:1 for key in nd if key not in st}
                st.update(extra)
    ans=0
    for (_,_,d),bits in st.items():
        if break_from is None or d:ans|=bits
    if not trace:return ans
    def get(c):
        assert break_from is None
        key=next(v for v,b in st.items() if b>>c&1);path=[key[0]]
        for j in reversed(range(K)):
            y,z,_=key;c-=cost(y);by=transitions(j)
            key=next((w,f,d) for (w,f,d),b in history[j].items() if b>>c&1 and y in by[w]
                     and pair(f,y,j+1)==z)
            path.append(key[0])
        assert c==cost(path[-1]);return [w[::-1] for w in reversed(path)]
    return ans,get

def check():
    from .fringe_suffix_bound import check as plateau
    certify_groups()
    assert all(BT[6,v]==B[6,v] for v in range(13))
    plateau()
    for axis in (1,2):
        for t in range(9):
            k,H,_=layout(t);s=k-4*H//3
            b=coupled(axis,s,4)
            assert b==spectrum(7,4,axis,False,None,True,s,True)
            _,oldcap=spectrum(7,4,axis,True,0,True,s,True)
            w=tuple(v[0] for v in oldcap((b&-b).bit_length()-1))
            assert traverse(axis,w,rooted_front(w))==[1]
            assert coupled(axis,s,5)==0
            assert coupled(axis,s,7,6)==0
            # Allow every intermediate component to find a root farther
            # west. The southern suffix must nevertheless advance.
            assert coupled(axis,s,7,0,break_from=s-7)==0
            b,get=coupled(axis,s,6,0,True,True)
            c=(b&-b).bit_length()-1;assert c==s+23
            path=get(c);j=s+4
            assert all(w==(448,)*6 for w in path[j:K]) and path[-1]==(192,)*6
            joined=path[:j+1]+[path[j]]*(14*t)+path[j+1:]
            # Fund the entire six-column transfer, not just the difference
            # from a cheaper four-column witness.
            g,tail=divmod(k-H-6-3,4);assert tail in (0,2)
            west3=198+72*t-(6*H-2)-c-10*g-5*(tail//2)-2*(t//8)
            cost=r=0
            for ref,h,d in [(0,3,west3)]+[(3 if j==0 else 7,4,12 if 1<=j<=t//8 else 10) for j in range(g)]+([(7,2,5)] if tail else []):
                w=west(axis,ref,h,d)
                assert physical(w[:13]+[w[12]]*(14*t)+w[13:],r,k,axis,True)==(d,0)
                r+=h;cost+=d
            assert r==k-H-6
            east=zip(*(row(k,q)[1] for q in reversed(range(H))))
            v,sealed=physical([(*a,*b) for a,b in zip(joined,east)],r,k,axis,True,require_roots=True)
            assert sealed==0 and cost+v==198+72*t
            # i=k-H-7 after seven new columns. For t+8u, i grows
            # by 28u. The plateau bound i-5<=3(j-1) still applies.
            i=k-H-7;u=max(0,(3*(s-8)+5-i)//28+1)
            print('axis',axis,'class',t,'closed4->5 and closed6->7 empty; open4->closed6',
                  c,'budget',cost+v,'max south start after 7',s-7,
                  'full extension excluded for t >=',t+8*u,'in class',flush=True)
if __name__=='__main__':
    import sys
    if len(sys.argv)>1:
        a,s,h=map(int,sys.argv[1:])
        b=coupled(a,s,h)
        print('five-column transfer' if h==5 else 'coupled transfer',a,s,h,'costs',
              [i for i in range(b.bit_length()) if b>>i&1])
    else:check()
