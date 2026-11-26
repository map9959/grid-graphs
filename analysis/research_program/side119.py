"""Replay both the near-optimal rail forest and literal side-119 target scores."""
from .zipper_rails import build,verify
from .delayed_right import terminal


def matching(n,edges,tree,full):
    """Give each edge to a parent choice in the primal or complementary dual."""
    def parents(adj,root):
        seen={root};q=[root];used=set()
        for u in q:
            for v,e in adj[u]:
                if v not in seen:seen.add(v);q.append(v);used.add(e)
        assert len(q)==len(adj) and len(used)==len(adj)-1
        return used
    primal=[[] for _ in range(n*n)]
    exterior=(n-1)**2;dual=[[] for _ in range(exterior+1)]
    def face(i,j):return i*(n-1)+j if 0<=i<n-1 and 0<=j<n-1 else exterior
    for e in edges:
        u,v=e;i,j=divmod(u,n)
        if e in tree:a,b,adj=u,v,primal
        else:
            assert not full.intersection(e)
            a=face(i,j);b=face(i-1,j) if v==u+1 else face(i,j-1)
            adj=dual
        adj[a].append((b,e));adj[b].append((a,e))
    a,b=parents(primal,0),parents(dual,exterior)
    assert a==tree and not a.intersection(b) and len(a)+len(b)==len(edges)
    return len(a),len(b)


def literal_scores(rows):
    # Complete the rail witness in the standard edge order. A unit face
    # with three tree edges permits swapping any one for the missing edge.
    n=len(rows);N=n*n
    edges=[(u,v) for u in range(N) for v in ([u+1] if u%n<n-1 else [])+([u+n] if u+n<N else [])]
    marked={i*n+j for i,row in enumerate(rows) for j,c in enumerate(row) if c=='#'}
    forced=[e for e in edges if marked.intersection(e)]
    parent=list(range(N));tree=set()
    def root(x):
        while x!=parent[x]:parent[x]=parent[parent[x]];x=parent[x]
        return x
    for e in forced+edges:
        a,b=map(root,e)
        if a!=b:parent[a]=b;tree.add(e)
    degree=[0]*N;grid=[0]*N
    for u,v in tree:degree[u]+=1;degree[v]+=1
    for u,v in edges:grid[u]+=1;grid[v]+=1
    score=sum(a==b for a,b in zip(grid,degree));steps=0
    assert score==4831
    while score>4753:
        before=score
        for i in range(n-1):
            for j in range(n-1):
                u=i*n+j
                face=[(u,u+1),(u,u+n),(u+1,u+n+1),(u+n,u+n+1)]
                absent=[e for e in face if e not in tree]
                if len(absent)!=1:continue
                add=absent[0]
                for drop in face:
                    if drop==add:continue
                    gain=set(add)-set(drop);lose=set(drop)-set(add)
                    delta=sum(degree[x]+1==grid[x] for x in gain)-sum(degree[x]==grid[x] for x in lose)
                    if delta!=-1:continue
                    tree.remove(drop);tree.add(add);score-=1;steps+=1
                    for x in gain:degree[x]+=1
                    for x in lose:degree[x]-=1
                    break
                if delta==-1 and score in (4754,4753):
                    full=set(range(N))-{x for e in edges if e not in tree for x in e}
                    assert len(full)==score and len(tree)==N-1
                    print('literal target',score,'verified full-degree set; primal/dual matched edges',
                          matching(n,edges,tree,full),'unit-face exchanges',steps)
                if score==4753:return
        assert score<before


def progression():
    terminal(1)
    def scores(t):
        n=35+42*t;k=11+14*t;F=5+7*t;B=3+5*t
        assert n-8-F==7*B+1
        count=n-2+1+(k+1)+F*k+B*(7*(k+1)+1)+(k+1)+(3*k+3+n)
        return count,3*k*k+7*k-2*t-1
    assert all(a==b for a,b in map(scores,range(3))) # quadratic identity
    for t in (0,1,2):
        n=35+42*t
        if n==35:continue # already certified separately
        v=verify(build(n))
        assert v[0]==v[-1]==scores(t)[0]
        print('side',n,'selected, acyclic forced edges, components, tree edges, full degree',v)


if __name__=='__main__':
    progression();literal_scores(build(119))
