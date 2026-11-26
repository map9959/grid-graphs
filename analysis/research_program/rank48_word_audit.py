"""Compare incremental slack debits with run, vacancy and edge counts on whole words."""
from itertools import product
from .skeleton_floor_words import priced


def compare(row):
    letters=[tuple(int(0<=x<len(row) and row[x]=='#') for x in (i-1,i,i+1))
             for i in range(0,len(row),3)]
    n=len(letters);H=[bool(l or r) for l,_,r in letters]
    active=[i for i,v in enumerate(H) if v];vac=[i for i,(_,z,_) in enumerate(letters) if not z]
    if not active and not vac:return
    hits=[int(i>0 and letters[i-1][2])+int(i+1<n and letters[i+1][0]) for i in range(n)]
    direct=sum(not H[i] and not hits[i] for i in vac)-int(not active)
    for i,j in zip(active,active[1:]):
        if j>i+1:direct+=int(j!=i+2 or i+1 not in vac or hits[i+1]!=2)
    for i in range(n-1):
        path=row[3*i:3*i+4];failed='..' in path
        missing=int(H[i] and path[1]=='.')+int(H[i+1] and path[2]=='.')
        direct+=missing-int(failed and missing>0)
    s=('pre' if active else 'p0',None,0);cost=0
    for i,a in enumerate(letters):
        s,q=priced(s,a,i==n-1);cost+=q
    assert direct==cost
    return cost


if __name__=='__main__':
    from .four_square import masks4
    from .pitch_skeleton_ledger import ledger
    words=sum(compare(''.join(w)) is not None for w in product('.#',repeat=16))
    import random
    rng=random.Random(48);ms=list(masks4());boards=0
    for _ in range(2000):
        rows=[['.']*10 for _ in range(10)]
        for y,x in product((0,6),repeat=2):
            m=rng.choice(ms)
            for a,b in product(range(4),repeat=2):
                if m>>(4*a+b)&1:rows[y+a][x+b]='#'
        rows=[''.join(r) for r in rows];tx=[''.join(r) for r in zip(*rows)]
        if '#..#..#..#' in rows+tx:continue
        for grid in (rows,tx):
            M,F,_,_,C,_=ledger(grid,empty='V')
            assert sum(compare(row) for row in grid[::3])<=40+F-C-M
        boards+=1
    print('whole-word comparisons',words,'side-ten ledger controls',boards,'both axes')
