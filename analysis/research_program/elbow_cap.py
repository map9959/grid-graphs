"""Optimize both arms of a free L around a rectangular comb core."""
from itertools import product
from subprocess import run

def build(n,w,h,phase=0,check=()):
    # Sweep down the western arm first, then east along the southern one.
    # The w-by-h elbow is swept by columns. Every noncore mark is free.
    F={i*n+j for i,j in product(range(n-h),range(w,n))
       if i==0 or (i>=2 and j%3==phase)}
    free=[i*n+j for i,j in product(range(n-h),range(w))]
    free.extend(i*n+j for j,i in product(range(n),range(n-h,n)))
    return contracted(n,free,F,check)

def contracted(n,free,F,check=()):
    """Exact forest kernel, with the caller supplying the vertex order."""
    order={u:i for i,u in enumerate(free)}
    par=list(range(n*n))
    def root(i):
        while i!=par[i]:par[i]=par[par[i]];i=par[i]
        return i
    def neigh(u):
        if u>=n:yield u-n
        if u+n<n*n:yield u+n
        if u%n:yield u-1
        if u%n<n-1:yield u+1
    for u in F:
        for v in neigh(u):
            if v in order or v in F and v<u:continue
            a,b=root(u),root(v);assert a!=b;par[a]=b
    es=[];fixed=[];term={};ids={}
    def node(m):es.append([]);fixed.append(m);return len(es)-1
    for u in free:
        links=[]
        for v in neigh(u):
            if v in order:
                if v in ids:links.append((ids[v],False))
            else:
                r=root(v)
                if r not in term:term[r]=node(0)
                links.append((term[r],v in F))
        ids[u]=node(-1);es[ids[u]]=links
    N=len(es)
    return [N,*[v for ls in es for v in (len(ls),*[i+1+int(a)*N for i,a in ls])],*fixed,*[ids[y*n+x] for y,x in check]],len(F)

def solve(n,w,h,p=0):
    data,k0=build(n,w,h,p)
    r=run(['target/annular_frontier'],input=' '.join(map(str,data)),text=True,capture_output=True)
    if r.returncode:raise RuntimeError(r.stderr)
    value,width,states=map(int,r.stdout.split());k=n//3;c=3*k*k+5*k+(3*k-13)//10
    print(n,w,h,p,'optimum',k0+value,'over comb',k0+value-c,'width',width,'peak',states,flush=True)
if __name__=='__main__':
    import sys
    solve(*map(int,sys.argv[1:]))
