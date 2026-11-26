"""Standalone replay of the 289-site witness, including a spanning-tree completion."""
from pathlib import Path


def verify():
    rows=Path(__file__).with_name('forest_28.txt').read_text().splitlines()
    n=len(rows)
    assert n==28 and all(len(r)==n and set(r)<={'.','#'} for r in rows)
    selected={i*n+j for i,r in enumerate(rows) for j,c in enumerate(r) if c=='#'}
    edges=[(u,v) for u in range(n*n) for v in
           ([u+1] if u%n<n-1 else [])+([u+n] if u+n<n*n else [])]
    forced=[e for e in edges if any(u in selected for u in e)]
    p=list(range(n*n));tree=set()
    def root(u):
        while u!=p[u]:u=p[u]
        return u
    def take(e):
        a,b=map(root,e)
        if a==b:return False
        p[a]=b;tree.add(e);return True
    for e in forced:assert take(e),('forced cycle',e)
    components=len({root(u) for u in range(n*n)})
    for e in edges:take(e)
    assert len(tree)==n*n-1 and len({root(u) for u in range(n*n)})==1
    lost={u for e in edges if e not in tree for u in e}
    assert set(range(n*n))-lost==selected and len(selected)==289
    print('selected',len(selected),'acyclic forced edges',len(forced),'components',components)
    print('spanning tree edges',len(tree),'full-degree vertices',n*n-len(lost))


if __name__=='__main__':verify()
