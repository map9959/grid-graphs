"""Uncapped lower tariff for an entire ordered seam word of a tile pair."""
from functools import lru_cache
from .arm_budget_bands import advance,cols
from .absolute_ports import actual_hops
from .ordered_ports import charts,typ,words
from .component_debt import star_union

def skipped(s):return int(bool(s&42))

@lru_cache(None)
def transition_prices():
    prices={};single={}
    for u in range(13):
        for v in range(13):
            for a,b,c,d in star_union(u,v):
                w=(a,c);y=(b,d);s=sym(w);t=sym(y)
                for z,p in ((s,w),(t,y)):
                    l=6-p[0].bit_count()-p[1].bit_count()
                    single[z]=min(single.get(z,100),l)
                v0=12-sum(x.bit_count() for x in (a,b,c,d))
                prices[s,t]=min(prices.get((s,t),100),v0)
    assert all(v==skipped(s) for s,v in single.items())
    assert all(v>=skipped(s)+skipped(t) for (s,t),v in prices.items())
    assert all(v>=2 for (s,t),v in prices.items() if s==0 and t and not skipped(t))
    return prices

def packet_bill(word):
    """Loss charged to skipped hops plus a maximum disjoint transition bill."""
    a=b=0;prices=transition_prices()
    for s,t in zip(word,word[1:]):
        a,b=b,max(b,a+prices[s,t]-skipped(s)-skipped(t))
    return b+sum(map(skipped,word))

@lru_cache(None)
def table(axis,r,j,d):
    # j indexes the top of the plaquette; r indexes its left side.
    out={}
    for a,b,c,e in charts(typ(r,38),typ(j,38),d):
        if any(min(x,38-x,y,38-y)>=4 and m&16 and m&(130 if axis==1 else 40)
               for x,y,m in ((r,j,a),(r,j+1,b),(r+1,j,c),(r+1,j+1,e))):continue
        out.setdefault((a,c),[]).append((b,e))
    return out

def rowchart(j,k):
    return j if j<7 else 38-(k-1-j) if k-1-j<=7 else 7

@lru_cache(None)
def sym(w):
    s=actual_hops(w[0]>>3,w[1])
    assert sum(bool(s>>(2*j)&3) for j in range(3))<=1
    return s

BASE=-1,tuple(range(7)),(0,)*6+(1,)
@lru_cache(None)
def push(z,w,end,r):
    side=int(r>0)|(32 if r<37 else 0)
    rim=sum(1<<x for x in range(6) if 3*r+x in (1,115))
    for b,m in enumerate(cols(w)):
        z=advance(z,m,63 if end and b==1 else rim,side)
        if z is None:break
    return z

def rims(r,d):
    if not 7<=r<=30:return None,None
    phase=4 if d>=5 else -4 if d<=-4 else None
    return words(2,True,phase),words(2,False)

def price(axis,i,k,q,word=None,reward=0):
    """min pair loss - reward * crossings; specified word fixes each absolute row."""
    r=rowchart(i,k);d=q-i
    north,south=rims(r,d)
    hist=[]
    def add(out,w,z,v):
        if z is not None and (not end or 2 not in z[2]):
            key=w,z
            val=v+6-sum(m.bit_count() for m in w)-reward*bool(sym(w))
            if key not in out or val<out[key][0]:out[key]=val,origin
    end=False;origin=None;st={}
    for w in table(axis,r,0,d):
        if (north is None or w in north) and (word is None or sym(w)==word[0]):
            add(st,w,push(BASE,w,True,r),0)
    hist.append(st)
    for row in range(1,k):
        t=table(axis,r,rowchart(row-1,k),d);nd={};end=row==k-1
        for origin,(v,_) in st.items():
            w,z=origin
            for y in t.get(w,()):
                if (end and south is not None and y not in south) or (word is not None and sym(y)!=word[row]):continue
                add(nd,y,push(z,y,end,r),v)
        st=nd;hist.append(st)
    if not st:return None
    key=min(st,key=lambda x:st[x][0]);val=st[key][0];path=[]
    for st in reversed(hist):path.append(key[0]);key=st[key][1]
    return val,tuple(reversed(path))
