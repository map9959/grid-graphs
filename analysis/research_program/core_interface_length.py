"""Arbitrary-length joint collar/core bound, using the width-eight potential."""
def penalty(bits):
    # Units of 1/7. Low pieces use seven times the width-eight upper.
    hi=lo=None
    for j in bits:
        if hi is None:hi,lo=140,102-4+21*j
        else:hi,lo=min(hi,lo+140),min(lo,hi+102)-4+21*j
    return min(hi,lo)

def bound(n,arms):
    m=n-20
    assert n%3==1 and n>=103 and len(arms)==4 and all(len(a)==m for a in arms)
    pen=sum(map(penalty,arms))
    return ((7*(n*n+4*n+23)+pen)*m+7*(16*n-170))//(7*(3*m+1))

def words(rows):
    n=len(rows);out=[]
    for _ in range(4):
        out.append([int(rows[8][x]=='#')+int(rows[9][x]=='#') for x in range(10,n-10)])
        rows=list(zip(*rows[::-1]))
    return out

def uniform(n):
    # Two full high/low sides and two sides split at 2n/3 as in
    # the mixed test. The transition offsets cost only a constant.
    m=n-20;l=2*n//3-10
    return bound(n,[[0]*m,[2]*m,[0]*l+[2]*(m-l),[2]*(m-l)+[0]*l])

if __name__=='__main__':
    from .collar_vacancies import comb
    for n in (103,163,403,1003):print('side',n,'mixed-word upper',uniform(n),'comb',comb(n))
