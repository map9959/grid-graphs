"""Exact one-layer extension of a frozen square using its noncrossing port partition."""
from functools import lru_cache
from .sparse_component_exchange import graph
from .extend_forest_28 import verify
from .wired_crop_exchange import ring

def canon(seq):
    return tuple(seq.index(x) for x in seq)

@lru_cache(32768)
def join(a,b):
    # Each table has (component root, first site, last site). The pieces
    # are disjoint before identifying the root and inserting the seam.
    u,v,p,ca=a;x,y,q,cb=b
    t=[*p,*(3+i for i in q)]
    colors=[*ca,*cb]
    def rt(i):
        while t[i]!=i:i=t[i]
        return i
    def unite(a,b):
        a,b=rt(a),rt(b)
        if a==b or colors[a] is not None and colors[b] is not None and colors[a]!=colors[b]:return False
        t[a]=b
        if colors[b] is None:colors[b]=colors[a]
        return True
    if not unite(3,0):return
    if x&2 and (v^x)&1:return
    if x&2 or (v|x)&1:
        if not unite(2,4):return
    rr=[rt(i) for i in (0,1,5)]
    return u,y,canon(rr),tuple(colors[q] for q in rr)

def concat(A,B):
    if A is None:return B
    C={}
    for a,(z,f) in A.items():
        for b,(w,g) in B.items():
            k=join(a,b)
            if k is not None and (k not in C or z+w>C[k][0]):C[k]=z+w,f|g
    return C

def path(labels,old,cycle=False,colors=None,repeat=None,forbidden=()):
    """All core port edges mandatory for marked backers or marked new sites."""
    last={a:i for i,a in enumerate(labels)};first={};stack=[];total=None
    for j,label in enumerate(labels):
        if first.setdefault(label,j)==j:stack.append([label,None])
        assert stack[-1][0]==label,'alternating boundary components cannot be planar'
        c=None if colors is None else colors[j]
        tag=2 if repeat is not None and repeat[j] else 0
        stack[-1][1]=concat(stack[-1][1],{(b|tag,b,(0,0,0),(c,c,c)) if b or old[j] else
                                          (b|tag,b,(0,1,1),(c,None,None)):
                                          (0 if tag else b,b<<j) for b in range(1 if j in forbidden else 2)})
        if j!=last[label]:continue
        _,part=stack.pop();finished={}
        for (a,b,p,t),val in part.items():
            key=a,b,(0,1,1 if p[1]==p[2] else 2),(None,t[1],t[2])
            if key not in finished or val[0]>finished[key][0]:finished[key]=val
        if stack:stack[-1][1]=concat(stack[-1][1],finished)
        else:total=concat(total,finished)
    return max(val for (a,b,p,t),val in total.items()
               if not(cycle and ((a|b)&1) and (p[1]==p[2] or
                   t[1] is not None and t[2] is not None and t[1]!=t[2])))

def extend(rows,side,outside=None,with_rows=False):
    """side 0..3: add an L to rotated input. side 4: add a whole ring."""
    m=len(rows);c=list(rows)
    for _ in range(side%4):
        c=list(map(''.join,zip(*c[::-1])))
        if outside is not None:outside={(x,m-1-y):g for (y,x),g in outside.items()}
    cyclic=side==4;n=m+1+cyclic;shift=1
    sites=ring(n) if cyclic else [(0,j) for j in range(m,-1,-1)]+[(i,0) for i in range(1,n)]
    F=graph(c,set()) if outside is None else None;lab=[];old=[];colors=[]
    for i,(y,x) in enumerate(sites):
        contacts=[(a-shift,b-shift) for a,b in ((y+1,x),(y-1,x),(y,x+1),(y,x-1))
                  if shift<=a<m+shift and shift<=b<m+shift]
        if contacts:
            (p,q),=contacts;lab.append(F.root((p,q)) if F else p*m+q);old.append(c[p][q]=='#')
            colors.append(outside[p,q] if outside is not None else None)
        else:lab.append(-i-1);old.append(False);colors.append(None)
    z,word=path(lab,old,cyclic,colors);out=[['.']*n for _ in range(n)]
    for i,row in enumerate(c,shift):out[i][shift:shift+m]=row
    for j,(y,x) in enumerate(sites):
        if word>>j&1:out[y][x]='#'
    out=[''.join(s) for s in out];v=verify(out)
    assert v[0]==sum(s.count('#') for s in c)+z
    return (z,v,out) if with_rows else (z,v)

def prices(rows,outside=None):
    m=len(rows);assert m%3==2 and m>=53
    k=(m+1)//3
    opt2=3*(k-1)**2+7*(k-1)-(k-6)//7-int(m%42==35)
    z=[extend(rows,s,outside)[0] for s in range(5)]
    bounds=[opt2,3*k*k+3*k-2-max(z[:4]),3*k*k+5*k+(k-5)//3-z[4]]
    return z,bounds

def direct(rows):
    """Test residue one itself against BOTH adjacent solved families."""
    n=len(rows);k=n//3;assert n%3==1 and k>=6
    gains=[extend(rows,s)[0] for s in range(5)]
    upper2=3*k*k+7*k-(k-5)//7-int((n+1)%42==35)
    upper0=3*(k+1)**2+3*(k+1)-2
    return gains,min(upper2-max(gains[:4]),upper0-gains[4])

def inner_reprice(rows):
    """Gain on the retained square itself, by reoptimizing only its rim."""
    m=len(rows);k=m//3
    old=sum(rows[y][x]=='#' for y,x in ring(m))
    z,tree=extend([s[1:-1] for s in rows[1:-1]],4)
    assert z>=old
    upper=3*k*k+7*k-(k-5)//7-int(m%42==35)
    return z-old,upper-(z-old),tree

def outside_labels(rows,h=10):
    """Partition induced by the collar AND the crossing edges, without a core edge."""
    from .sparse_component_exchange import Forest
    n=len(rows);m=n-2*h;F=Forest(n)
    def inner(y,x):return h<=y<n-h and h<=x<n-h
    for y in range(n):
        for x in range(n):
            for i,j in ((y+1,x),(y,x+1)):
                if max(i,j)>=n or inner(y,x) and inner(i,j):continue
                if rows[y][x]=='#' or rows[i][j]=='#':assert F.join((y,x),(i,j))
    return {p:F.root((p[0]+h,p[1]+h)) for p in ring(m)}

def projected_ledger(rows,pi):
    m=len(rows);M={p for p in pi if rows[p[0]][p[1]]=='#'}
    D=sum((i in (0,m-1))+(j in (0,m-1)) for i,j in M)
    # Two forests on the ports have zero intersection of their
    # identification spaces. Apply this to all ports and then the marked ones.
    c=len(pi)-len(set(pi.values()))+1
    r=len(M)-len({pi[p] for p in M})+bool(M)
    K=m*m+D-c
    return min((K-r)//3,K*m//(3*m+1))

def run_floor(m,required,forbidden):
    """A line segment of one carrier can cover only one segment-id per axis."""
    pts=set(required);lines={}
    for (y,x),g in required.items():
        for axis,(i,j) in enumerate(((y,x),(x,y))):
            lines.setdefault((axis,i,g),[]).append(j)
    ids={v:[None,None] for v in pts}
    for (axis,i,g),_ in lines.items():
        start=0
        for j in range(m):
            v=(i,j) if axis==0 else (j,i)
            if v in forbidden or v in pts and required[v]!=g:start=j+1
            if v in pts and required[v]==g:ids[v][axis]=(i,g,start)
    # A real collection of carriers is a vertex cover. Every matching
    # is a lower bound on its size, including across different labels.
    adj={}
    for a,b in ids.values():adj.setdefault(a,[]).append(b)
    mate={}
    def augment(a,seen):
        for b in adj[a]:
            if b in seen:continue
            seen.add(b)
            if b not in mate or augment(mate[b],seen):
                mate[b]=a;return True
        return False
    return sum(augment(a,set()) for a in adj)

def split_floor(m,M,cls):
    """Two distinct end components on the same normal line force a break.

    The private right-hand witness of each tip is either an interior
    isolate or is rescued by a nondistinguished carrier. See the proof.
    """
    best=(0,0)
    for swap in (False,True):
        p=lambda y,x:(x,y) if swap else (y,x)
        used=set();last=-2;xs=[]
        for x in range(1,m-2):
            a,b=p(0,x),p(m-1,x)
            if x-last<3 or a not in M or b not in M:continue
            if any(p(i,x+j) in M for i in (0,m-1) for j in (-1,1)):continue
            labels={cls[a],cls[b]}
            if len(labels)<2 or labels&used:continue
            used|=labels;last=x;xs.append(x)
        b=len(xs);spared=set();off={i+d for i in xs for d in (1,2)}
        for x in range(1,m-1):
            if x in off:continue
            for y in (0,m-1):
                v=p(y,x)
                if v in M and cls[v] not in used and not any(p(y,x+j) in M for j in (-1,1)):
                    spared.add(cls[v])
        best=max(best,(2*b+len(spared)+(2*b+2)//3,b))
    return best

def accounting(rows):
    """Only the rim word and its partition are used after extracting F."""
    m=len(rows);F=graph(rows,set());R=set(ring(m));M={v for v in R if rows[v[0]][v[1]]=='#'}
    cls={v:F.root(v) for v in R};count={}
    for g in cls.values():count[g]=count.get(g,0)+1
    D=sum((y in (0,m-1))+(x in (0,m-1)) for y,x in M)
    required={v:cls[v] for v in M}
    for y,x in R-M:
        nb={(i,j) for i,j in ((y+1,x),(y-1,x),(y,x+1),(y,x-1)) if 0<=i<m and 0<=j<m}
        if count[cls[y,x]]>1 and not nb&M:
            (u,)=nb-R
            assert rows[u[0]][u[1]]=='#'
            required[u]=cls[y,x]
    forbid=(R-M)|{(y+dy,x+dx) for y,x in required for dy in (-1,1) for dx in (-1,1)}
    assert not (forbid&required.keys())
    c=len(count);r=run_floor(m,required,forbid);K=m*m+D-c
    # Every remaining forced isolate found in the visible collar is
    # a separate component not yet counted by the boundary partition.
    for y,x in forbid:
        if 0<y<m-1 and 0<x<m-1 and all(v in forbid for v in ((y+1,x),(y-1,x),(y,x+1),(y,x-1))):K-=1
    tax,b=split_floor(m,M,cls)
    # Do not count separately an isolate already used as a tip witness.
    split=(m*m+D-c-tax)//3
    return min((K-r)//3,K*m//(3*m+1),split),(D,c,r,len(required),b)

if __name__=='__main__':
    from .arbitrary_collar_transfer import obstruction_board,marks
    from .comb_cap_transfer import construct
    for name,board in [('mixed',obstruction_board(103,True)[1]),('comb',construct(103,4))]:
        c=[s[10:-10] for s in board[10:-10]];T=marks(board)-marks(c)
        z,u=prices(c)
        a,info=accounting(c);assert a>=marks(c)
        print(name,'ten',T,'ports gains',z,'83 bounds',u,
              'ledger',a,info,'transferred',T+min(*u,a))
        pi=outside_labels(board);gz,gu=prices(c,pi);ga=projected_ledger(c,pi)
        print('collar alone: gains',gz,'ledger',ga,'transferred',T+min(*gu,ga))
        g,ru,tree=inner_reprice(c);print('inside-rim gain',g,'conditional upper',ru,'parent',T+ru,'tree',tree)
        zz,du=direct(board);print('direct outward comparison on original side',zz,du)
