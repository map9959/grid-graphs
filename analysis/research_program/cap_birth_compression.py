"""Height-independent reduction of a pitch cap by its number of extra marked runs."""
from .reflected_pitch_rank import ledger
from .comb_cap_transfer import construct


def stats(cap):
    n=len(cap[0]);r=(n+2)//3
    assert cap[0]=='#..'*(r-1)+'#' and len({len(w) for w in cap})==1
    cyc,j=ledger(cap);assert cyc==0
    born=[sum(x=='#' and u!='#' and (i==0 or w[i-1]!='#')
              for i,(u,x) in enumerate(zip(prev,w))) for prev,w in zip(cap,cap[1:])]
    return j,sum(w.count('#')-r for w in cap[1:]),born


def shorten(cap):
    cap=list(cap);j0,b0,old=stats(cap);E=sum(old)
    while len(cap)>1:
        j,b,born=stats(cap)
        if not born[-1]:cap.pop()
        else:
            k=next((i+1 for i in range(len(born)-2) if not any(born[i:i+3])),None)
            if k is None:break
            del cap[k]
        t,bonus,new=stats(cap)
        assert t<=j and bonus>=b and sum(new)<=sum(born)
    assert len(cap)-1<=3*E
    return cap


def floors(k,j):
    # Least integer bonus that violates the desired tariff.
    b=9 if not j else (90+7*j)//10+1
    # 3b=2k+j-E-(n-t)-holes-extra_components. Two disjoint far
    # corner pairs force at least two incidences missing (depth >=2).
    return b,2*k+j-3*b-2


def audit():
    from itertools import product
    # Enumerate actual small-width row paths, including all three-row
    # deletions even when not needed for the final height inequality.
    n=4;words=[''.join(w) for w in product('.#',repeat=n)]
    active=[['#..#']];checked=0
    for _ in range(5):
        nxt=[]
        for cap in active:
            for w in words:
                c=cap+[w]
                if ledger(c)[0]:continue
                j,b,a=stats(c)
                for t in range(len(a)-2):
                    if not any(a[t:t+3]):
                        v,z,new=stats(c[:t+1]+c[t+2:])
                        assert v<=j and z>=b and sum(new)<=sum(a);checked+=1
                nxt.append(c)
        active=nxt
    print('physical three-row deletions checked',checked)
    cap=construct(103,4)[2:];c=shorten(cap)
    print('wired comb cap',len(cap)-1,'->',len(c)-1,'rank,bonus',stats(c)[:2])
    assert stats(c)[:2]==(0,8)
    print('arbitrary-depth violations forced to depth <=12:',
          [(j,*floors(34,j)) for j in range(34) if 3*floors(34,j)[1]<=12])


if __name__=='__main__':audit()
