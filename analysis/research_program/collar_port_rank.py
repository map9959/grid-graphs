"""Bound crop repair debt from the discarded collar, without fixing the retained core."""
from .blocked_rim_exchange import pos,lock_windows,exchange
from .crop_end_coupling import locked_fringe
from .sparse_component_exchange import graph
from .sparse_component_exchange import Forest
from .collar_vacancies import comb
from .extend_forest_28 import verify

def merge_rank(labels,groups):
    """How many independent unions of old labels are demanded by new groups?"""
    par={};first={};r=0
    def rt(i):
        while i in par:i=par[i]
        return i
    for x,g in zip(labels,groups):
        a,b=rt(x),rt(first.setdefault(g,x))
        if a!=b:par[a]=b;r+=1
    return r

def projected(rows,h,W):
    n=len(rows);m=n-2*h
    # Only these removed sites, the double posts and the two seam bits
    # are inspected. Depth two of the smaller square is not inspected.
    collar=[''.join(v if min(y,x,n-1-y,n-1-x)<h else '.' for x,v in enumerate(row))
            for y,row in enumerate(rows)]
    F=graph(collar,set());labels=[];groups=[];ends=[];eg=[];pads=set()
    posts=0;private=-1
    for i,(side,l,r) in enumerate(W):
        assert h>=1 and 2<=l and r<=m-3
        pad={pos(m,side,d,j) for d in range(3) for j in range(l-1,r+2)}
        assert not pads&pad;pads|=pad
        xs=list(range(l+1,r,3));assert r==xs[-1]+1 and len(xs)>=2
        def site(d,x):return pos(n,side,h+d,h+x)
        def marked(d,x):
            y,j=site(d,x);return rows[y][j]=='#'
        assert all(marked(0,x) and marked(1,x) for x in xs)
        z=[F.root(site(-1,x)) for x in xs];posts+=len(z)
        # All possible backing contacts and lateral leaf contacts have
        # a label in z. An unsupported seam gets a private old label.
        for x,q in ((l-1,z[0]),(r+1,z[-1])):
            if marked(0,x):ends.append(q);eg.append(i)
            else:z.append(private);private-=1
        labels.extend(z);groups.extend([i]*len(z))
    mu1=merge_rank(labels,groups);mu2=merge_rank(ends,eg)
    return posts,mu1,mu2,posts-mu1-mu2

def arbitrary_windows(rows,h,W):
    """Upper bound repair debt from the old inside partition for arbitrary words.
    Read the collar, the two editable rows, and the two seam words only.
    The backing row may be arbitrary, simultaneously on all windows.
    """
    n=len(rows);m=n-2*h;known=set();inside=set();pads=set();windows=[]
    for y in range(n):
        for x in range(n):
            if min(y,x,n-1-y,n-1-x)<h:inside.add((y,x))
    for side,l,r in W:
        assert 2<=l<=r-3 and r<=m-3
        def at(d,j):return pos(n,side,h+d,h+j)
        pad={at(d,x) for d in range(3) for x in range(l-1,r+2)}
        assert not pads&pad;pads|=pad
        block=[[at(d,x) for x in range(l-1,r+2)] for d in (0,1)]
        for z in block:inside.update(z[1:-1]);known.update(z)
        windows.append(block)
    known.update(inside)
    M={v for v in known if rows[v[0]][v[1]]=='#'}
    F=Forest(n)
    for i,j in inside:
        for q in ((i+1,j),(i,j+1)):
            if q in inside and ((i,j) in M or q in M):assert F.join((i,j),q)
    A=[];G=[];A2=[];G2=[];old=length=0;private=-1
    for i,(a,b) in enumerate(windows):
        old+=sum(v in M for v in a[1:-1]+b[1:-1]);length+=len(a)-2
        for j in range(1,len(a)-1):
            # A backing mark at normal depth 2 is impossible if either
            # tangential neighbour in the depth-one word is marked.
            possible=b[j-1] not in M and b[j+1] not in M
            lateral=(j==1 and b[0] in M) or (j==len(a)-2 and b[-1] in M)
            if possible or lateral:A.append(F.root(b[j]));G.append(i)
        for p,q in ((a[1],a[0]),(a[-2],a[-1])):
            if p in M or q in M:id0=F.root(p)
            else:id0=private;private-=1
            A.append(id0);G.append(i)
            if q in M:A2.append(id0);G2.append(i)
    mu1=merge_rank(A,G);mu2=merge_rank(A2,G2)
    return length-old,mu1,mu2,length-old-mu1-mu2

def partitions(n):
    if n==0:yield ();return
    for p in partitions(n-1):
        for i in range(max(p,default=-1)+2):yield p+(i,)

def nullity(a,b):
    # Bipartite incidence graph with one edge per port.
    return len(a)-len(set(b))-merge_rank(a,b)

def crosscheck():
    checked=0
    # Multiple windows, shared collar classes, expensive and cheap
    # contacts. Exhaust ALL exterior partitions, including parallel ports.
    new=(0,0,0,1,1,1);hi=(0,2,3,5);sub=lambda v:tuple(v[i] for i in hi)
    pp=list(partitions(6))
    for old in pp:
        pred=merge_rank(old,new)+merge_rank(sub(old),sub(new))
        worst=0
        for ext in pp:
            if nullity(old,ext):continue
            checked+=1
            worst=max(worst,nullity(new,ext)+nullity(sub(new),sub(ext)))
        assert worst==pred
    print(checked,'compatible triples; exact worst weighted debt for all',len(pp),'old partitions')

def physical_words():
    # Free old words, unknown returns, marked/blank seams and lateral contacts.
    n=11;h=1;W=[(0,2,5)];checked=0;kinds=set()
    for seam in (set(),{(1,2),(1,7)},{(2,2),(2,7)}):
        for back in (set(),{(3,3),(3,6)}, {(3,3),(3,6)}|{(5,j) for j in range(2,8)},
                     {(3,2),(3,7)}|{(5,j) for j in range(2,8)}):
            for mask in range(256):
                M=seam|back|{
                    (1+i//4,3+i%4) for i in range(8) if mask>>i&1}
                r=[''.join('#' if (y,x) in M else '.' for x in range(n)) for y in range(n)]
                try:verify(r)
                except AssertionError:continue
                c=[s[1:-1] for s in r[1:-1]];out,d=exchange(c,W)
                g=arbitrary_windows(r,h,W)
                assert g[-1]<=d[-2]<=d[-1]==verify(out)[0]-sum(s.count('#') for s in c)
                kinds.add(tuple(d[2:4]));checked+=1
    print('arbitrary two-row words:',checked,'physical comparisons; rejected contact counts',sorted(kinds))

def audit():
    n=103;r=locked_fringe(n);orig=verify(r)
    for h in (3,6):
        c,W=lock_windows(r,h);m=n-2*h;k=m//3
        b,mu1,mu2,G=projected(r,h,W)
        assert arbitrary_windows(r,h,W)==(b,mu1,mu2,G)
        v=verify(c);loss=orig[0]-v[0]
        U=3*k*k+5*k+(k-5)//3
        new,data=exchange(c,W)
        assert data[-1]>=G and verify(new)[0]>=v[0]+G
        print('side',m,'posts / merge ranks / core-independent gain:',b,mu1,mu2,G,
              'smaller upper',U-G,'parent upper',loss+U-G)
        if h==6:assert loss+U-G<=comb(n)
    # Same collar and double posts; change the entire retained core.
    # Each pair of seam feet now returns via the depth-four bar. On the
    # last side one backed post also returns there.
    alt=[list(s) for s in r]
    for i in range(6,n-6):
        for x in range(6,n-6):alt[i][x]='.'
    for side,l,end in W:
        def mark(d,x):
            i,j=pos(n,side,6+d,6+x);alt[i][j]='#'
        for x in (l-1,end+1):mark(0,x);mark(2,x)
        for x in range(l-1,end+2):mark(4,x)
        for x in range(l+1,end,3):mark(0,x);mark(1,x)
        if side==3:mark(2,l+13)
    alt=[''.join(s) for s in alt];orig2=verify(alt)
    out,price=exchange([s[6:-6] for s in alt[6:-6]],W)
    assert projected(alt,6,W)==(32,5,4,23) and price==(64,32,1,4,23,23)
    assert arbitrary_windows(alt,6,W)==(32,5,4,23)
    print('changed backing: joint debt 9 physically realized; gain 23',orig2,verify(out))
    crosscheck()
    physical_words()
if __name__=='__main__':audit()
