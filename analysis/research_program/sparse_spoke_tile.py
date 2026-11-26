"""Arbitrary-exterior replacement test for a punctured three-column wing."""
from itertools import product

def canon(v):return tuple(v.index(x) for x in v)

def initial(opened):
    # Indices: permanent side root, two top sites, two bottom-frontier sites.
    dp={}
    for v in range(4):
        # With a nonempty word both sites belong to the same end component.
        a,b=(1,1) if v else (1,2)
        if v&2 and not opened:a=b=0
        dp[v,v,canon([0,a,b,a,b])]=v.bit_count()
    return dp

def advance(dp,opened,prev=None,unit=1,premium=0):
    nd={}
    for (start,old,part),z in dp.items():
        for v in range(4):
            if v&(old<<1|old>>1):continue
            q=[*part,5,6]
            def rt(i):
                while i!=q[i]:i=q[i]
                return i
            def join(i,j):
                i,j=rt(i),rt(j);q[i]=j;return i!=j
            if any((old|v)>>s&1 and not join(3+s,5+s) for s in (0,1)):continue
            if v and not join(5,6) or v&2 and not opened and not join(0,6):continue
            key=start,v,canon([rt(i) for i in (0,1,2,5,6)])
            score=z+unit*v.bit_count()+premium*int(opened and bool(v&2))
            if key not in nd or nd[key]<score:
                nd[key]=score
                if prev is not None:prev[key]=(start,old,part)
    return nd

def layer(H,holes):
    dp=initial(0 in holes)
    for y in range(1,H):dp=advance(dp,y in holes)
    return dp

def refines(p,q):
    return all(p[i]!=p[j] or q[i]==q[j] for i,j in product(range(5),repeat=2))

def price(H,hole):
    return loss(layer(H,set()),layer(H,{hole}))

def loss(clean,old):
    worst=-100;bad=[]
    for (a,b,q),z in old.items():
        m=max((s for (i,j,p),s in clean.items() if (i,j)==(a,b) and refines(p,q)),default=-1000)
        if z-m>worst:worst=z-m;bad=[]
        if z-m==worst:bad.append((a,b,q,z,m))
    return worst,bad

def all_lengths():
    # Remove every root link except in the first and last two rows.
    # The released partition refines that from any subset of omissions.
    clean=opened=layer(2,set());seen={}
    for k in range(100):
        C=advance(advance(clean,False),False);D=advance(advance(opened,False),False)
        w,_=loss(C,D);assert w==0
        def normalized(dp):
            m=max(dp.values());return frozenset((s,v-m) for s,v in dp.items()),m
        c,u=normalized(clean);d,v=normalized(opened);key=c,d
        if key in seen:
            j,x,y=seen[key];assert u-x==v-y
            print('two-column wing: all heights, worst loss 0;',
                  'repeated interiors',j,k,'common shift',v-y,'prefix states',len(c),len(d))
            return
        seen[key]=k,u,v
        clean=advance(clean,False);opened=advance(opened,True)
    raise AssertionError('no exact recurrence')
if __name__=='__main__':all_lengths()
