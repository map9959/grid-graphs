"""Delete one row and one column of labels in a constructive residue-zero square."""
from itertools import product
from collections import Counter

from analysis.patterns.diagonal_patterns import residue_zero_pattern


def check(rows):
    n=len(rows)
    p=list(range(n*n))
    def root(v):
        while p[v]!=v:
            p[v]=p[p[v]]
            v=p[v]
        return v
    cycles=0
    for i,j in product(range(n),repeat=2):
        for a,b in ((i+1,j),(i,j+1)):
            if a<n and b<n and "." in (rows[i][j],rows[a][b]):
                u,v=root(n*i+j),root(n*a+b)
                if u==v:
                    cycles+=1
                else:
                    p[u]=v
    return sum(s.count(".") for s in rows),cycles


def census(n):
    rows=residue_zero_pattern(n+1)
    assert check(rows)[1]==0
    k=(n-2)//3
    target=3*k*k+7*k
    out=Counter()
    for i,j in product(range(n+1),repeat=2):
        small=[s[:j]+s[j+1:] for r,s in enumerate(rows) if r!=i]
        f,rank=check(small)
        out[f-target,rank]+=1
    return max(d for d,r in out if not r), min((r for d,r in out if d>=0),default=None)


if __name__=="__main__":
    for n in [5,8,11,14]:
        print(n,"best feasible excess, minimum cycle rank at target or better:",census(n))
