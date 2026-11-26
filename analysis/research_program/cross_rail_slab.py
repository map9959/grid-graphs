"""Replace a slab by complete rails after trimming a column and deleting one row."""
from .extend_forest_28 import verify


def roots(rows):
    w=len(rows[0]);p=list(range(len(rows)*w))
    def root(a):
        while p[a]!=a:p[a]=p[p[a]];a=p[a]
        return a
    for i,row in enumerate(rows):
        for j,m in enumerate(row):
            a=i*w+j
            for b,val in ((a-1,row[j-1] if j else '.'),(a-w,rows[i-1][j] if i else '.')):
                if b==a-1 and j==0 or b==a-w and i==0:continue
                if m==val=='.':continue
                u,v=root(a),root(b);assert u!=v;p[u]=v
    return [root(i) for i in range(len(p))]


def cap_rank(left,right):
    """Two partitions, each including every unmarked singleton contact."""
    a={v:j for j,v in enumerate(sorted(set(left)))}
    b={v:j+len(a) for j,v in enumerate(sorted(set(right)))}
    p=list(range(len(a)+len(b)))
    def root(x):
        while p[x]!=x:p[x]=p[p[x]];x=p[x]
        return x
    q=0
    for u,v in zip(left,right):
        x,y=root(a[u]),root(b[v])
        if x==y:q+=1
        else:p[x]=y
    return q


def cut(rows,a,b,side=0,phase=0):
    """a,b are retained gate rows; one strictly intermediate row is removed."""
    n=len(rows);k=n//3;w=n-1
    assert n==3*k+1 and 0<=a<b<n and b>=a+3
    trimmed=[r[1:] if side else r[:-1] for r in rows]
    cols=list(range(phase,w,3));pitch=''.join('#' if j in cols else '.' for j in range(w))
    E=sum(rows[i][0 if side else -1]=='#' for i in [*range(a+1),*range(b,n)])
    G=0
    for i in (a,b):
        clean=''.join(x if y=='#' else '.' for x,y in zip(trimmed[i],pitch))
        G+=trimmed[i].count('#')-clean.count('#');trimmed[i]=clean
    u,v=roots(trimmed[:a+1]),roots(trimmed[b:])
    q=cap_rank([u[a*w+j] for j in cols],[v[j] for j in cols])
    H=b-a-1;S=sum(r.count('#') for r in rows[a+1:b])
    out=trimmed[:a+1]+[pitch]*(H-1)+trimmed[b:]
    return out,(E,G,S-k*H,q),k+E+G+S-k*H+q


def repair(rows):
    """Find a physical cycle, break it at a marked turn, and repeat."""
    n=len(rows);cells=[c=='#' for r in rows for c in r];dropped=0
    while True:
        adj=[[] for _ in cells];p=list(range(n*n))
        def root(a):
            while p[a]!=a:p[a]=p[p[a]];a=p[a]
            return a
        cycle=None
        for a in range(n*n):
            for b in ([a+1] if a%n<n-1 else [])+([a+n] if a//n<n-1 else []):
                if not (cells[a] or cells[b]):continue
                u,v=root(a),root(b)
                if u!=v:p[u]=v;adj[a].append(b);adj[b].append(a);continue
                prev={a:None};todo=[a]
                while b not in prev:
                    t=todo.pop()
                    for z in adj[t]:
                        if z not in prev:prev[z]=t;todo.append(z)
                cycle=[b]
                while cycle[-1]!=a:cycle.append(prev[cycle[-1]])
                break
            if cycle:break
        if not cycle:break
        for j,t in enumerate(cycle):
            l=cycle[j-1];r=cycle[(j+1)%len(cycle)]
            if abs(l-t)!=abs(r-t):
                assert cells[t] and not(cells[l] and cells[r])
                cells[t]=False;dropped+=1;break
        else:raise AssertionError('no turn on a grid cycle')
    return [''.join('#' if z else '.' for z in cells[i:i+n]) for i in range(0,n*n,n)],dropped


def end_cut(rows,H,x,phase):
    """Rescore a discarded top band against the cap's actual terminal classes."""
    n=len(rows);k=n//3;w=n-1
    assert n==3*k+1 and 4<=H<n and 0<=x<n and phase in range(3)
    cols=range(phase,w,3)
    cap=[list(r[:x]+r[x+1:]) for r in rows[H:]]
    E=sum(r[x]=='#' for r in rows[H:])
    G=sum(v=='#' and j%3!=phase for j,v in enumerate(cap[0]))
    cap[0]=[v if j%3==phase else '.' for j,v in enumerate(cap[0])]
    # Keep the subdividable edges first. Then a failed edge has just
    # one owner, as in the single-cross proof.
    p=list(range(len(cap)*w))
    def rt(a):
        while p[a]!=a:p[a]=p[p[a]];a=p[a]
        return a
    pending=[]
    for i,row in enumerate(cap):
        for j,m in enumerate(row):
            a=i*w+j
            for b in ([a-w] if i else [])+([a-1] if j else []):
                bi,bj=divmod(b,w);v=cap[bi][bj]
                if v==m=='.':continue
                if bi==i and j==x and rows[H+i][x]=='.' and v!=m:
                    pending.append((a,b,a if m=='#' else b));continue
                u,t=rt(a),rt(b);assert u!=t;p[u]=t
    paid=0
    for a,b,owner in pending:
        u,t=rt(a),rt(b)
        if u!=t:p[u]=t
        else:
            i,j=divmod(owner,w)
            assert cap[i][j]=='#'
            cap[i][j]='.';paid+=1
    labs=roots(cap);seen=set();bar=['#']*w
    for j in cols:
        if labs[j] in seen:bar[j]='.'
        seen.add(labs[j])
    joins=k-len(seen)
    pitch=''.join('#' if j in cols else '.' for j in range(w))
    out=[''.join(bar),'.'*w]+[pitch]*(H-3)+[''.join(r) for r in cap]
    S=sum(r.count('#') for r in rows[:H])
    terms=(S-k*H,E,G,paid,joins)
    assert sum(r.count('#') for r in rows)-sum(r.count('#') for r in out)==sum(terms)
    return out,terms


def normalize(rows,a,b):
    n=len(rows);pitch='#..'*(n//3)+'#'
    assert n==len(pitch) and b-a>=4
    arr=rows[:]
    e=sum(r.count('#')-r[::3].count('#') for r in rows[a:b+1])
    Z=sum(r[::3].count('.') for r in rows[a+1:b])
    u=sum(any(rows[i][j]==rows[i+1][j]=='.' for i in range(a,b)) for j in range(0,n,3))
    for i in (a,b):arr[i]=''.join(x if y=='#' else '.' for x,y in zip(arr[i],pitch))
    arr[a+1:b]=[pitch]*(b-a-1)
    out,paid=repair(arr);tree=verify(out)
    assert paid<=u and all(row==pitch for row in out[a+1:b])
    assert tree[0]-sum(r.count('#') for r in rows)==Z-e-paid
    return (Z,u,e,paid),tree


if __name__=='__main__':
    from .cross_minor_refill import shell_control
    from .cross_minor_price import construct,scattered
    for board,a,b in [(scattered(construct(103,4)),2,96),(shell_control(103),37,65)]:
        total=sum(r.count('#') for r in board)
        trials=[cut(board,a,b,t,h) for t in range(2) for h in range(3)]
        out,terms,bound=min(trials,key=lambda z:z[-1])
        arr,dropped=repair(out);tree=verify(arr)
        assert dropped<=terms[-1] and total-tree[0]<=bound
        print(total,(a,b),terms,'guaranteed loss',bound,'repairs',dropped,'tree',tree)
        out,terms=end_cut(board,50,17,1)
        print('one end',terms,'loss',sum(terms),'tree',verify(out))
        print('mixed-slab normalization',normalize(board,a,b))
