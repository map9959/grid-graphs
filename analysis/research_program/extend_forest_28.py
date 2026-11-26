"""Repeat the side-28 construction by widening rails and inserting one 3-row band."""
from pathlib import Path


def extend(rows):
    n=len(rows)
    assert n>=28 and n%3==1 and all(len(r)==n and r[9]==r[10] for r in rows)
    assert [i for i,r in enumerate(rows) if r[10]=='#']==list(range(0,n,3))
    wide=[r[:10]+r[10]*3+r[10:] for r in rows]
    assert wide[2]==wide[4]=='#'+'.'*(n+1)+'#'
    assert wide[3]=='#.'+'#'*(n-2)+'..#'
    return wide[:2]+wide[2:5]+wide[2:]


def verify(rows,full_rows=False):
    n=len(rows)
    s={i*n+j for i,r in enumerate(rows) for j,c in enumerate(r) if c=='#'}
    edges=[(i,v) for i in range(n*n) for v in
           ([i+1] if i%n<n-1 else [])+([i+n] if i+n<n*n else [])]
    forced=[e for e in edges if any(u in s for u in e)]
    p=list(range(n*n));tree=set()
    def root(i):
        while p[i]!=i:
            p[i]=p[p[i]]
            i=p[i]
        return i
    for e in forced+edges:
        u,v=map(root,e)
        if u!=v:p[u]=v;tree.add(e)
    assert set(forced)<=tree and len(tree)==n*n-1
    full=set(range(n*n))-{u for e in edges if e not in tree for u in e}
    assert s<=full
    if full_rows:return [''.join('#' if i*n+j in full else '.' for j in range(n)) for i in range(n)]
    return len(s),len(forced),n*n-len(forced),len(tree),len(full)


if __name__=='__main__':
    import argparse
    args=argparse.ArgumentParser()
    args.add_argument('side',type=int,default=31,nargs='?')
    args.add_argument('--grid',action='store_true')
    opt=args.parse_args()
    assert opt.side>=28 and opt.side%3==1
    rows=Path(__file__).with_name('forest_28.txt').read_text().splitlines()
    for n in range(28,opt.side+1,3):
        if n>28:rows=extend(rows)
        selected,forced,components,edges,full=verify(rows)
        k=(n-1)//3
        assert selected==3*k*k+5*k+1
        print(f'side {n}: selected {selected}, forced edges {forced}, forest components {components}, '
              f'spanning tree edges {edges}, full-degree vertices {full}')
    if opt.grid:print('\n'.join(rows))
