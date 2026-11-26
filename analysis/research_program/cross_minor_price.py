"""Single-row/column compression to the solved residue, with physical repair."""
from .extend_forest_28 import verify
from .comb_cap_transfer import construct


def repair(rows,y,x):
    n=len(rows);s=n-1
    small=[list(row[:x]+row[x+1:]) for i,row in enumerate(rows) if i!=y]
    parent=list(range(s*s))
    def root(i):
        while i!=parent[i]:
            parent[i]=parent[parent[i]];i=parent[i]
        return i
    def join(a,b):
        u,v=root(a),root(b)
        if u==v:return False
        parent[u]=v
        return True
    paid=[];pending=[]
    for i,row in enumerate(small):
        for j,m in enumerate(row):
            for u,v in ((i+1,j),(i,j+1)):
                if u>=s or v>=s:continue
                q=small[u][v]
                if q==m=='.':continue
                a=i*s+j;b=u*s+v
                seam_v=i!=u and u==y
                seam_h=j!=v and v==x
                unsupported=(seam_v and rows[y][j+(j>=x)]=='.' or
                             seam_h and rows[i+(i>=y)][x]=='.')
                if unsupported and q!=m:
                    pending.append((a,b,a if m=='#' else b))
                else:assert join(a,b)
    for a,b,site in pending:
        if not join(a,b):paid.append(site)
    for site in set(paid):
        i,j=divmod(site,s);small[i][j]='.'
    return [''.join(row) for row in small],len(paid),len(set(paid))


def demo(rows):
    n=len(rows);k=n//3
    pitch='#..'*k+'#'
    no_pitch=all(pitch not in rr for rr in (rows,[''.join(c) for c in zip(*rows)]))
    counts=[row.count('#') for row in rows];cols=list(map(sum,zip(*[[c=='#' for c in row] for row in rows])))
    pairs=sorted((counts[i]+cols[j]-(rows[i][j]=='#'),i,j) for i in range(n) for j in range(n))
    def line_cost(rr,i):
        return rr[i].count('#')+sum(0<i<n-1 and m=='.' and rr[i-1][j]!=rr[i+1][j]
                                    for j,m in enumerate(rr[i]))
    cheap=sum(min(line_cost(rr,i) for i in range(n))
              for rr in (rows,[''.join(c) for c in zip(*rows)]))
    best=None
    for loss,i,j in pairs:
        if best and loss>=best[0]:break
        rr,rank,cost=repair(rows,i,j)
        record=(loss+cost,loss,rank,cost,i,j)
        if best is None or record<best:best=record;out=rr
    replay=verify(out)
    assert replay[0]==sum(counts)-best[0] and best[0]<=cheap
    print('side',n,'no spanning pitch',no_pitch,'marks',sum(counts),'line bound',cheap,
          'best (loss, erased, rank, repaired, y, x)',best,'tree',replay)


def scattered(rows):
    """Break different teeth; enforce each break by omitting a physical tree edge."""
    n=len(rows);k=n//3;pitch='#..'*k+'#'
    broken={i*n+3*(1+i%(k-1)) for i,s in enumerate(rows) if s==pitch}
    keep={i*n+j for i,row in enumerate(rows) for j,c in enumerate(row) if c=='#'}-broken
    edges=[(a,b) for a in range(n*n) for b in
           ([a+1] if a%n<n-1 else [])+([a+n] if a//n<n-1 else [])]
    parent=list(range(n*n))
    def root(a):
        while a!=parent[a]:parent[a]=parent[parent[a]];a=parent[a]
        return a
    tree=set()
    for a,b in sorted(edges,key=lambda e:keep.isdisjoint(e)):
        if a in broken and b==a+1:continue
        u,v=root(a),root(b)
        if u!=v:parent[u]=v;tree.add((a,b))
    assert len(tree)==n*n-1
    full=set(range(n*n))-{z for e in edges if e not in tree for z in e}
    assert keep<=full and full.isdisjoint(broken)
    return [''.join('#' if i*n+j in full else '.' for j in range(n)) for i in range(n)]


if __name__=='__main__':
    r=construct(103,4)
    demo(r)
    demo(scattered(r))
    # A physically completed, laterally shifted crop. Check actual tree marks.
    r=verify(['.'+row[:-1] for row in r],True)
    demo(r)
