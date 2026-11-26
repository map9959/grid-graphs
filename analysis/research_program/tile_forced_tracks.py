"""Intersect forced crop connectivity over all live words in each tile block."""
from functools import lru_cache
from itertools import product

@lru_cache(None)
def partition(masks,rows,cols):
    p=list(range(40))
    def rt(u):
        while p[u]!=u:u=p[u]
        return u
    def edge(u,v):p[rt(u)]=rt(v)
    X=[masks[(i//3)*2+j//3]>>(3*(i%3)+j%3)&1 for i,j in product(range(6),repeat=2)]
    for i,j in product(range(6),repeat=2):
        if rows[i]<0 or cols[j]<0:continue
        u=6*i+j
        if X[u]:
            tag=rows[i] if rows[i] in (0,2) else cols[j]
            if tag<4:edge(u,36+tag)
        if i<5 and rows[i+1]>=0 and (X[u] or X[u+6]):edge(u,u+6)
        if j<5 and cols[j+1]>=0 and (X[u] or X[u+1]):edge(u,u+1)
    return tuple(rt(i) for i in range(40))

def forced(n,types,catalogs,dom):
    K=(n-2)//3-1;p=list(range(n*n+4));terms=range(n*n,n*n+4)
    def rt(i):
        while p[i]!=i:p[i]=p[p[i]];i=p[i]
        return i
    def edge(a,b):p[rt(a)]=rt(b)
    @lru_cache(None)
    def common(t,mask,R,C):
        part=[0]*40
        for k,w in enumerate(catalogs[t]):
            if mask>>k&1:
                u=partition(w,R,C)
                if len(set(u[-4:]))<4:continue
                codes={};part=[codes.setdefault(pair,len(codes)) for pair in zip(part,u)]
        return tuple(part)
    for z,(i,j) in enumerate(product(range(K),repeat=2)):
        if not dom[z]:continue
        def layer(v,side):return -1 if v<2 or v>n-3 else side if v==2 else side^2 if v==n-3 else 4
        R=tuple(layer(1+3*i+a,0) for a in range(6));C=tuple(layer(1+3*j+b,3) for b in range(6))
        u=common(types[z],dom[z],R,C)
        sites=[(1+3*i+a)*n+1+3*j+b for a,b in product(range(6),repeat=2)]+list(terms)
        rep={}
        for x,k in zip(sites,u):edge(x,rep.setdefault(k,x))
    result=[rt(i) for i in terms]
    print('certified-catalogue forced root classes',result,'contradiction',len(set(result))<4)
    return len(set(result))<4
