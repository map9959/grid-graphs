"""One-contact cut test: keep the actual rooted/unrooted port through a column."""
from collections import defaultdict
from functools import lru_cache
from .component_debt import links,step,contacts,west_joins,typ,cols
from .missing_arm_rim import words

def flip(m):return m>>6|m&56|(m&7)<<6
def joins(w):return west_joins(w),west_joins(tuple(flip(m) for m in reversed(w)))

def single(axis,r,phase=None,pump=None,cap=32,any_length=False,signature=False,price=None):
    K=38;rim=7<=r<=31
    north=words(3,True,phase);south=words(3,False)
    def by(j):return links(3,r,typ(j,K),tuple(min(x,K-x)>=4 for x in (j,j+1)),axis)
    @lru_cache(None)
    def local(y,z,f,j):
        end=j in (0,K);v=step(z,y,end,r)
        if v is None or (j==K and 2 in v[2]):return
        g,ds=contacts(f,y,end,r)
        if j==K:ds+=tuple(x for x in g[2] if x&1)
        if 1 in ds:return
        sig=sum(1<<x for x in set(ds) if x!=9)
        a,b=joins(y);return v,g,sig,a,b
    @lru_cache(None)
    def debit(y,a,b):
        # Sum prefix differences at the three physical sites. Over the
        # complete column this is right hop row minus left hop row; a
        # missing hop is placed after the last row.
        d=0
        for m in cols(y):
            def hops(m):return ((m>>2)&(m>>3)&1)+((m>>1)&~(m>>2)&(m>>3)&1)+((m>>2)&~(m>>3)&(m>>4)&1)
            a+=hops(m)
            b+=((m>>5)&(m>>6)&1)+((m>>4)&~(m>>5)&(m>>6)&1)+((m>>5)&~(m>>6)&(m>>7)&1)
            d+=a-b
        return price[0]*(3-y[1].bit_count())+price[1]*d
    base=-1,tuple(range(10)),(0,)*9+(1,);cbase=-1,(0,1,2),(0,0,0)
    mask=(1<<(cap+1))-1 if cap is not None else None
    def move(src,j):
        nd={};tab=by(j)
        for (w,z,f,sig,a,b),bits in src.items():
            if pump is not None and j==pump:
                stay=local(w,z,f,pump)
                if (w[1].bit_count()!=3 or w not in tab[w] or
                    stay is None or stay!=(z,f,0,0,0)):continue
            for y in tab[w]:
                if rim and j+1==K and y not in south:continue
                result=local(y,z,f,j+1)
                if result is None:continue
                v,g,s,aa,bb=result
                if a+aa>1 or b+bb>1:continue
                key=y,v,g,s|sig,a+aa,b+bb
                if price is not None:
                    d=bits+debit(y,a,b)
                    if key not in nd or d<nd[key]:nd[key]=d
                else:
                    d=1 if mask is None else (bits<<(3-y[1].bit_count()))&mask
                    if d:nd[key]=nd.get(key,0)|d
        return nd
    st={}
    for w in by(0):
        if rim and w not in north:continue
        res=local(w,base,cbase,0)
        if res is not None:
            v,g,s,a,b=res
            if a<=1 and b<=1:st[w,v,g,s,a,b]=debit(w,0,0) if price is not None else 1 if mask is None else 1<<(3-w[1].bit_count())
    for j in range(K):
        st=move(st,j)
        if any_length and j==18:
            delta=st.copy()
            rounds=0
            while delta:
                sub={}
                for key,v in move(delta,j).items():
                    if price is not None:
                        if key not in st or v<st[key]:st[key]=sub[key]=v
                    else:
                        v&=~st.get(key,0)
                        if v:sub[key]=v;st[key]=st.get(key,0)|v
                delta=sub
                rounds+=1
                if rounds>100:raise ValueError('no bounded closure')
    ans=defaultdict(int)
    for (_,_,_,s,a,b),bits in st.items():
        for incoming in ((1,2) if a else (0,)): # 1: already rooted; 2: still unresolved
            outgoing=0
            for tag in (3,5,7,11,13,15):
                if not s>>tag&1:continue
                roots=int(bool(tag&8))+int(bool(tag&2) and incoming==1)
                if roots>1 or (not tag&4 and not roots):break
                if tag&4:outgoing=1 if roots else 2
            else:
                assert bool(outgoing)==bool(b)
                key=(incoming,outgoing,s) if signature else (incoming,outgoing)
                if price is not None:
                    if key not in ans or bits<ans[key]:ans[key]=bits
                else:ans[key]|=bits
    return dict(ans)
def check():
    carry=(1,1,1<<7),(2,2,1<<7)
    swap=2,2,(1<<11)|(1<<5)
    for axis in (1,2):
        args=dict(axis=axis,r=7,phase=-4,cap=None,any_length=True,signature=True)
        assert set(single(**args))=={*carry,swap}
        for price,expected in (((1,0),(3,3)),((-1,0),(-3,-3)),((0,1),(0,4))):
            vals=single(**args,price=price)
            assert vals=={carry[0]:expected[0],carry[1]:expected[0],swap:expected[1]}
        assert not single(axis,37,cap=None,any_length=True)
        print('axis',axis,'sparse east: deficit exactly 3; carry drift >=0; tooth-and-rebirth drift >=4')
        print('penultimate column: no terminal state with <=1 hop on both sides')
if __name__=='__main__':check()
