"""Sufficient local tests for erasing three actual rows without introducing a cycle."""
from .comb_cap_transfer import construct
from .extend_forest_28 import verify

def band(rows,a,width=3):
    # A and E on opposite sides of the deleted band become consecutive.
    n=len(rows);w=len(rows[0]);b=a+1+width
    m=lambda y,x:0<=y<n and 0<=x<w and rows[y][x]=='#'
    damage=set()
    for x in range(w):
        if not(m(a,x) or m(b,x)):continue
        if all(m(y,x) or m(y+1,x) for y in range(a,b)):continue
        if any(not any(m(y+dy,x+dx) for dy,dx in ((0,0),(0,1),(0,-1),(out,0)))
               for y,out in ((a,-1),(b,1))):continue
        for y in (a,b):
            if m(y,x):damage.add((y,x))
    lost=sum(r.count('#') for r in rows[a+1:b])+len(damage)
    return lost,damage

def contract(rows,a,damage,width=3):
    return [''.join('.' if (y,x) in damage else c for x,c in enumerate(r))
            for y,r in enumerate(rows) if not a<y<a+1+width]

def audit(n,width=3):
    rows=construct(n,4);score=sum(r.count('#') for r in rows);best=None
    # Try either order. Equal row bands in a long stripe have identical
    # effect apart from translation; just use the cheapest four first cuts.
    for R in (rows,list(zip(*rows))):
        prices=[(*band(R,a,width),a) for a in range(n-width-1)]
        for lost,damage,a in sorted(prices,key=lambda q:(q[0],q[2]))[:4]:
            mid=list(zip(*contract(R,a,damage,width)))
            more,D,b=min(((*band(mid,b,width),b) for b in range(n-width-1)),key=lambda q:(q[0],q[2]))
            if best is None or best[0]>lost+more:best=lost+more,contract(mid,b,D,width),a,b,len(damage)+len(D)
    loss,small,a,b,repairs=best
    check=verify(small);assert check[0]==score-loss
    print(n,'trim',width,'cuts',a,b,'local repairs',repairs,'loss',loss,'tree',check,flush=True)
if __name__=='__main__':
    for n in (43,73,103):
        for width in (1,2,3):audit(n,width)
