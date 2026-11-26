"""Replay the mixed-rank reflection ledger on finite strips without wiring the input."""
from .comb_cap_transfer import construct


def ledger(rows, wired=False):
    h,w=len(rows),len(rows[0])
    parent=list(range(h*w))
    def root(i):
        while i!=parent[i]:
            parent[i]=parent[parent[i]]
            i=parent[i]
        return i
    def join(i,j):
        i,j=root(i),root(j)
        parent[i]=j
        return i==j
    cycles=0
    for i,row in enumerate(rows):
        for x,m in enumerate(row):
            a=i*w+x
            if x and '#' in (m,row[x-1]):cycles+=join(a,a-1)
            if i and '#' in (m,rows[i-1][x]):cycles+=join(a,a-w)
    teeth=list(range(0,w,3))
    rank=len(teeth)-len({root(x) for x in teeth})
    if wired:
        for x in teeth[1:]:cycles+=join(0,x)
    return cycles,rank


def check(cap):
    assert ledger(cap)[0]==0
    j=ledger(cap)[1]
    chain=cap
    budget=0
    for copies in range(2,7):
        tile=[s[::-1] for s in cap] if copies%2==0 else cap
        budget+=sum(a[0]==b[0]=='.' for a,b in zip(tile,tile[1:]))
        chain=[a+b[1:] for a,b in zip(chain,tile)]
        c,r=ledger(chain)
        assert c<=budget and c+r<=copies*j+budget
        assert ledger(chain,True)[0]==c+r
    return j


if __name__=='__main__':
    from random import Random
    rng=Random(103)
    rows=construct(103,4);cut=50
    ranks=set()
    for p in (0,.001,.005,.01,.03,.1):
        rr=[''.join('.' if i!=cut and rng.random()<p else x for x in s)
            for i,s in enumerate(rows)]
        a,b=check(rr[cut::-1]),check(rr[cut:])
        ranks.add((a,b))
        v=sum(sum(x=='.' and y=='#' for x,y in zip(col,col[1:]))+int(col[-1]=='.')
              for cap in (rr[cut::-1],rr[cut:]) for col in
              ([s[x] for s in cap] for x in (0,-1)))
        k=34
        bound=103*35+(12*k+15*(a+b)-10*v)//20
        assert sum(s.count('#') for s in rr)<=bound
    pitch=rows[cut];blank='.'*103
    for split in (24,48,75):
        top='#'*(split+1)+'.'*(102-split)
        bot='.'*split+'#'*(103-split)
        rr=[top,blank,pitch,blank,bot]
        assert ledger(rr)[0]==0
        ranks.add((check(rr[2::-1]),check(rr[2:])))
    print('six-copy physical seams verified; rank pairs',sorted(ranks))
    print('103 upper by total join deficit 0..6, before vacancy credit:',
          [103*35+(27*34-15*d)//20 for d in range(7)])
