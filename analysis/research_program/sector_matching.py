"""Temperley edge owners for a sector-score model; NW is the omitted vertex."""
from itertools import combinations,product
from .square_dual_physical import DIR

def add(f,pool,X,n):
    def exactly_one(v):
        f.append(v)
        for a,b in combinations(v,2):f.append([-a,-b])
    edges={}
    for i,j in product(range(n),repeat=2):
        u=i*n+j;choices=[]
        for d,(a,b) in enumerate(DIR):
            r,c=i+a,j+b
            if not(0<=r<n and 0<=c<n):continue
            e=tuple(sorted((u,r*n+c)));owners=edges.setdefault(e,[])
            if u:
                p=pool.id(('primal',u,d));owners.append(p);choices.append(p)
                f.append([-pool.id(('a',u,d)),p])
        if u:exactly_one(choices)
    for i,j in product(range(n-1),repeat=2):
        u=i*n+j;vs=[u,u+1,u+n+1,u+n];choices=[]
        for a,b in zip(vs,vs[1:]+vs[:1]):
            e=tuple(sorted((a,b)));p=pool.id(('dual',i,j,e));edges[e].append(p);choices.append(p)
            f.extend([[-p,-X[a]],[-p,-X[b]]])
        exactly_one(choices)
    for owners in edges.values():exactly_one(owners)

def append_existing(n,target):
    """Stream the saved score CNF. Recognize and validate each five-clause edge block."""
    from pysat.formula import CNF,IDPool
    from pathlib import Path
    from collections import deque
    import shutil
    src=Path(f'target/sector{n}_{target}.cnf')
    arcs={};last=deque(maxlen=5)
    with src.open('rb') as s:
        _,_,nv,nc=s.readline().split();nv,nc=int(nv),int(nc)
        for line in s:
            if line.count(b' ') not in (3,2):last.clear();continue
            c=tuple(map(int,line.split()[:-1]));last.append(c)
            if len(last)!=5:continue
            p,x,y,q,r=last
            if len(x)!=3 or len(y)!=3:continue
            U,a,b=x;V=y[0]
            if not (0<-U<-V<=n*n and a>n*n and b>n*n and y==(V,a,b) and p==(-a,-b) and q==(-a,-U,-V) and r==(-b,-U,-V)):continue
            u,v=-U-1,-V-1;d=0 if v-u==1 else 1
            assert v-u in (1,n) and ('a',u,d) not in arcs
            arcs['a',u,d]=a;arcs['a',v,(d+2)%4]=b
    assert len(arcs)==4*n*(n-1)
    vp=IDPool(start_from=nv+1)
    class Pool:
        def id(self,k):return arcs[k] if k[0]=='a' else vp.id(k)
    f=CNF();add(f,Pool(),range(1,n*n+1),n)
    dest=src.with_stem(src.stem+'_matching')
    with dest.open('wb') as out,src.open('rb') as s:
        s.readline();out.write(f'p cnf {vp.top} {nc+len(f.clauses)}\n'.encode())
        shutil.copyfileobj(s,out)
        for c in f.clauses:out.write((' '.join(map(str,c))+' 0\n').encode())
    print('mapped arcs',len(arcs),'added owner variables',vp.top-nv,'added clauses',len(f.clauses),'final CNF',vp.top,nc+len(f.clauses),flush=True)

def check_tree(n):
    from .comb_cap_transfer import construct
    from .extend_forest_28 import verify
    from pysat.formula import CNF,IDPool
    from collections import defaultdict
    rows=construct(n,4);score=verify(rows)
    marked={i*n+j for i,j in product(range(n),repeat=2) if rows[i][j]=='#'}
    adj=defaultdict(list);dual=defaultdict(list)
    edges=[(u,v) for u in range(n*n) for v in ([u+1] if u%n<n-1 else [])+([u+n] if u//n<n-1 else [])]
    par=list(range(n*n))
    def rt(u):
        while u!=par[u]:par[u]=par[par[u]];u=par[u]
        return u
    tree=set()
    for u,v in sorted(edges,key=lambda e:not any(t in marked for t in e)):
        a,b=rt(u),rt(v)
        if a!=b:
            par[a]=b;tree.add((u,v));adj[u].append(v);adj[v].append(u)
    def face(i,j):return (i,j) if 0<=i<n-1 and 0<=j<n-1 else None
    for e in set(edges)-tree:
        u,v=e;i,j=divmod(u,n);a=face(i,j);b=face(i-1,j) if v==u+1 else face(i,j-1)
        dual[a].append((b,e));dual[b].append((a,e))
    vp=IDPool();X=[vp.id(('m',u)) for u in range(n*n)];f=CNF();add(f,vp,X,n)
    true={X[u] for u in marked};q=[0];seen={0}
    for u in q:
        for v in adj[u]:
            if v in seen:continue
            q.append(v);seen.add(v)
            d=DIR.index((u//n-v//n,u%n-v%n));true.add(vp.id(('primal',v,d)))
            if u in marked or v in marked:true.add(vp.id(('a',v,d)))
    q=[None];seen={None}
    for u in q:
        for v,e in dual[u]:
            if v in seen:continue
            seen.add(v);q.append(v);true.add(vp.id(('dual',*v,e)))
    assert len(seen)==1+(n-1)**2 and all(any((abs(x) in true)==(x>0) for x in c) for c in f.clauses)
    print('physical tree replay',score,'owner clauses verified',len(f.clauses))

if __name__=='__main__':
    import sys
    if '--check-tree' in sys.argv:check_tree(int(sys.argv[1]))
    else:append_existing(*map(int,sys.argv[1:]))
