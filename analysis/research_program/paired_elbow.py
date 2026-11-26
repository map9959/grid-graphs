"""A diagonal family of paired L terminals feeding two perpendicular free caps."""
from .elbow_cap import product,run

def chart(n,h,corner='h',width=0):
    s=n-h
    F={i*n+j for i,j in product(range(s),repeat=2) if min(i,j)%3==0 and
       (i==j or not((j==i+1 and corner=='h') or (i==j+1 and corner=='v')))}
    free=[]
    for a in range(s):
        free.extend(i*n+a for i in range(s,n))
        free.extend(a*n+j for j in range(s,n))
        if width:free.extend(i*n+j for i,j in product(range(max(0,a-width),a+1),repeat=2)
                             if max(i,j)==a)
    free.extend(i*n+j for i,j in product(range(s,n),repeat=2))
    order=set(free);F-=order
    p=list(range(n*n))
    def rt(a):
        while p[a]!=a:p[a]=p[p[a]];a=p[a]
        return a
    def nb(u):
        if u>=n:yield u-n
        if u<n*n-n:yield u+n
        if u%n:yield u-1
        if u%n<n-1:yield u+1
    for u in F:
        for v in nb(u):
            if v in order or v in F and v<u:continue
            a,b=rt(u),rt(v);assert a!=b;p[a]=b
    ids={};fixed=[];es=[];terms={}
    def node(v):fixed.append(v);es.append([]);return len(es)-1
    for u in free:
        ls=[]
        for v in nb(u):
            if v in order:
                if v in ids:ls.append((ids[v],False))
            else:
                r=rt(v)
                if r not in terms:terms[r]=node(0)
                ls.append((terms[r],v in F))
        ids[u]=node(-1);es[ids[u]]=ls
    N=len(es);inp=[N,*[v for ls in es for v in (len(ls),*[a+1+b*N for a,b in ls])],*fixed]
    r=run(['target/annular_frontier'],input=' '.join(map(str,inp)),text=True,capture_output=True)
    if r.returncode:print('frontier resource limit',h,width,r.stderr);return
    v,w,num=map(int,r.stdout.split());k=n//3
    print(n,h,width,'score',v+len(F),'relative to comb',v+len(F)-3*k*k-5*k-(3*k-13)//10,'frontier',w,num,flush=True)
if __name__=='__main__':
    import sys
    chart(int(sys.argv[1]),int(sys.argv[2]),width=int(sys.argv[3]) if len(sys.argv)>3 else 0)
