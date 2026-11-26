"""Exterior forest ledger for a strict pitch frame; no completion of unknown pins."""
from collections import Counter
from .comb_cap_transfer import construct

def audit(rows,box,ledger=False):
    n=len(rows);a,b,l,r=box;H=b-a+1;W=r-l+1;p=(W+2)//3
    assert 0<a<b<n-1 and 0<l<r<n-1 and W==3*p-2
    rail=range(l,r+1,3)
    mark=lambda i,j:rows[i][j]=='#'
    assert all(mark(y,x)==(x in rail) for y in (a,b) for x in range(l,r+1))
    solid=[x for x in rail if all(mark(y,x) for y in range(a,b+1))]
    assert l in solid and r in solid
    inside=lambda y,x:a<=y<=b and l<=x<=r
    par=list(range(n*n));deg=Counter();ports=[]
    def root(i):
        while par[i]!=i:par[i]=par[par[i]];i=par[i]
        return i
    R=M=outer=0
    for i in range(n):
        for j in range(n):
            if inside(i,j):continue
            f=mark(i,j);M+=f
            outer+=f*((i in (0,n-1))+(j in (0,n-1)))
            R+=f and not any(0<=u<n and 0<=v<n and not inside(u,v) and mark(u,v)
                             for u,v in ((i-1,j),(i,j-1)))
            for u,v in ((i+1,j),(i,j+1),(i-1,j),(i,j-1)):
                if not (0<=u<n and 0<=v<n and (f or mark(u,v))):continue
                if inside(u,v):ports.append((i*n+j,u*n+v,f));continue
                if (i,j)>(u,v):continue
                x,y=root(i*n+j),root(u*n+v);assert x!=y;par[x]=y
                deg[i*n+j]+=1;deg[u*n+v]+=1
    Q=len({root(x) for x,_,_ in ports});t=sum(f for _,_,f in ports)
    assert len(ports)==2*H+2*p and R>=t
    outside=n*n-H*W
    c=sum(root(i)==i and not inside(*divmod(i,n)) for i in range(n*n))
    assert 3*M==outside+outer+t-R-c
    # Exterior-only components not incident to a port remain a separate debit.
    reserve=c-Q
    if ledger:return outer-len(solid)-(R-t)-reserve
    assert Q>=2*H+len(solid)+1
    bound=(outside+outer-2*H-len(solid)-1-(R-t)-reserve)//3
    actual=sum(row.count('#') for row in rows)
    assert M<=bound and actual<=H*p+bound
    return len(solid),len(ports),Q,M,bound,actual,H*p+bound

if __name__=='__main__':
    for n in (43,73,103):
        print(n,audit(construct(n,4),(3,n-10,3,n-4)))
