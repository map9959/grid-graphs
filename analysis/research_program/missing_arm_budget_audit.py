"""Independent graph/score checks for blocks that lack an opposing arm."""
from collections import Counter
from functools import lru_cache
from .arm_budget_bands import B,physical,typ,transpose
from .joined_arm_budget import west
from .missing_arm_blocks import transfer
from .missing_arm_rim import words

def minima(bits):return [(v&-v).bit_length()-1 for v in bits]

def fan_word(k,i,M):
    p=1+i//3
    assert 1<=p<M<k-1
    return [6]+[7]*(p-1)+[(48,33,3)[i%3]]+[56]*(M-p-1)+[24]+[73]*(k-M-1)

def fan_catalogue():
    # Every plaquette of consecutive fan columns occurs in one of these
    # compressed charts. Remove copies of the constant (7,7), (56,56)
    # and (73,73) slices, keeping each end's six position types.
    # Test the switch near either fringe as well as in the bulk.
    for p0 in range(1,10):
        for gap in (12,):
            M=p0+gap
            for phase in range(3):
                i=3*(p0-1)+phase
                if 1+(i+1)//3>=M:continue
                k=M+2
                u,v=(fan_word(k,x,M) for x in (i,i+1))
                for j in range(k-1):
                    w=(u[j],v[j],u[j+1],v[j+1])
                    assert tuple(map(transpose,w)) in B[typ(j,k-1),6]
    print('fan plaquettes: all three switch phases and clipped fringes checked')

def rim_piece(axis,r,h,c,k,reference):
    p=west(axis,reference,h,c);t=(k-39)//14
    p=p[:13]+[p[12]]*(14*t)+p[13:]
    assert physical(p,r,k,axis,True)==(c,0)
    return p

def fan_budget(t):
    k=39+14*t;H=12+8*t;R=k-8-H;M=k-2
    r=tot=0
    groups=[(3,20),(4,26),*((4,28) for _ in range(3))]
    groups+=([(4,32)]*3)*(t//2)
    if t%2:groups.extend([(4,32),(2,16)])
    for h,c in groups:
        rim_piece(1,r,h,c,k,min(r,7));r+=h;tot+=c
    assert r==R
    p=list(zip(*(fan_word(k,i,M) for i in range(H))))
    assert physical(p,r,k,1,True)==(3*H,0)
    # Independently traverse the entire unsliced physical rectangle.
    # Each marked component is classified by how many teeth it contains
    # and whether it is exposed at each of the two exterior cuts.
    n=3*k;h=3*H;X={(3*i+l//3,3*j+l%3) for j,w in enumerate(p) for i,m in enumerate(w)
                     for l in range(9) if m>>l&1}
    seen=set();counts=Counter()
    for z in X:
        if z in seen:continue
        q=[z];seen.add(z);roots=0;left=right=False
        for i,j in q:
            roots+=((i,j) in X and j in (1,n-2))
            left|=i==0;right|=i==h-1
            for v in ((i-1,j),(i+1,j),(i,j-1),(i,j+1)):
                if 0<=v[0]<h and 0<=v[1]<n and v not in seen and ((i,j) in X or v in X):
                    q.append(v);seen.add(v)
        counts[roots,left,right]+=1
    assert sum(v for (a,_,_),v in counts.items() if a==1)==H
    assert counts[0,True,True]==k-M-1 and sum(counts.values())==H+k-M-1
    r+=H;tot+=3*H
    for ref,c in ((31,10),(35,22)):
        rim_piece(1,r,4,c,k,ref);r+=4;tot+=c
    assert (r,tot)==(k,198+72*t)
    print('fan k',k,'joined width',H,'spanning unrooted components',k-M-1,'exact deficit',tot)

@lru_cache(None)
def crossing_template(a,h,c):
    bits,get=transfer(a,h,False,True,6*h,all_missing=True,trace=True,
                      rim=-4,cross_both=True)
    assert all(bits[(1<<h)-1]>>v&1 for v in range(5*h,6*h+1))
    return get(c)

def block_budget(a,t):
    k=39+14*t;n=k-15;g,h=divmod(n,5);sizes=[5]*g
    if h<=2 and h:sizes[-1:]=[3,2+h]
    elif h:sizes.append(h)
    assert sum(sizes)==n
    surplus=198+72*t-62-5*n
    r=tot=0
    for ref,h,c in ((0,3,20),(3,4,10)):
        rim_piece(a,r,h,c,k,ref);r+=h;tot+=c
    for h in sizes:
        e=min(h,surplus);surplus-=e;c=5*h+e
        w=crossing_template(a,h,c)
        p=w[:19]+[w[18]]*(14*t)+w[19:]
        assert physical(p,r,k,a,True)==(c,0)
        assert set(p[0])=={6}
        assert all(not (v[:13]==(6,)+(7,)*12 and v[-12:]==(448,)*11+(192,)) for v in zip(*p))
        for i in (1,h-1):
            # Direct physical mark pairs: at least one forced path joins
            # marked sites across each inner cut, not just isolated leaves.
            def sites(col):
                return {(b//3,3*j+b%3) for j,row in enumerate(p) for b in range(9) if row[col]>>b&1}
            left,right=sites(i-1),sites(i)
            assert any((x+dx-3,y+dy) in right for x,y in left for dx,dy in ((1,0),(2,0),(1,1),(1,-1)))
        r+=h;tot+=c
    for ref,c in ((31,10),(35,22)):
        rim_piece(a,r,4,c,k,ref);r+=4;tot+=c
    assert (r,surplus,tot)==(k,0,198+72*t)
    print('axis',a,'k',k,'two-cut blocks',len(sizes),'exact deficit',tot)

def check():
    fan_catalogue()
    for t in (0,1,2,5):fan_budget(t)
    assert words(1,True,-4)=={(6,)} and (6,) not in words(1,True,4)
    for a in (1,2):
        m=minima(transfer(a,6,False,False,36,True,True,rim=True))
        assert m==[36,36,36,36,15]
        for sides,want in enumerate(([0]*4,[0,1,1,1],[0,0,0,1],[1]*4)):
            assert transfer(a,5,False,limit=None,free_length=True,rim=-4,outer_sides=sides)==want
        print('axis',a,'six-column minima by missing count',m,'east-of-star grounded block impossible')
        for t in range(6):block_budget(a,t)

if __name__=='__main__':check()
