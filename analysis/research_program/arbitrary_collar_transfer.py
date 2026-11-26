"""Six-layer crop charge with an unrestricted four-layer annular refill."""
from ast import literal_eval
from pathlib import Path
from subprocess import run
from .collar_vacancies import comb
from .crop_end_coupling import locked_fringe
from .comb_cap_transfer import construct
from .extend_forest_28 import verify
from .zipper_rails import build
from .wired_crop_exchange import ring
from .sparse_component_exchange import Forest
from .collar_closed import witness
from functools import lru_cache

BIN=Path(__file__).resolve().parents[2]/'target/collar_bend'

def engine(args,rows=()):
    lines=run([BIN,*map(str,args)],input='\n'.join(rows),text=True,
              capture_output=True,check=True).stdout.splitlines()
    return literal_eval(lines[0]),[tuple(map(int,s.split())) for s in lines[1:]]

def marks(rows):return sum(s.count('#') for s in rows)

@lru_cache(None)
def optimal_four(m):
    # Known attained 4-layer optimum; any successful seam mask suffices.
    from .collar_closed import closed
    score,_,mask=closed(20,True)
    r,_=witness(20,mask,score)
    assert r[9]==r[10] and all(s[9]==s[10] for s in r)
    rr=r[:10]+[r[9]]*(m-20)+r[10:]
    return tuple(s[:10]+s[9]*(m-20)+s[10:] for s in rr)

def transplant(c,r):
    """Pay for genuinely redundant forced edges, with two-owner edges priced first."""
    m=len(c);B={(y,x) for y,s in enumerate(r) for x,v in enumerate(s) if v=='#'}
    core={(y,x) for y in range(4,m-4) for x in range(4,m-4) if c[y][x]=='#'}
    F=Forest(m);arcs=[]
    for y in range(m):
        for x in range(m):
            p=y,x
            for q in ((y+1,x),(y,x+1)):
                if max(q)>=m:continue
                if p in core or q in core:assert F.join(p,q)
                else:
                    own={p,q}&B
                    if own:arcs.append((len(own),p,q,own))
    lost=set();beta=heavy=0
    for w,p,q,own in sorted(arcs,reverse=True):
        if not F.join(p,q):lost|=own;beta+=1;heavy+=w==2
    M=core|(B-lost)
    out=[''.join('#' if (y,x) in M else '.' for x in range(m)) for y in range(m)]
    assert len(lost)<=beta+heavy
    return len(B)-len(lost),out,(beta,heavy)

def charge(rows):
    n=len(rows);m=n-12;k=m//3
    assert n%3==1 and k>=18
    c=[s[6:-6] for s in rows[6:-6]]
    inner=[s[4:-4] for s in c[4:-4]]
    ten=marks(rows)-marks(inner);R=marks(rows)-marks(c)
    A=sum(engine(('outer',10,6),rows)[0])
    parts,M=engine(('repair',4,0),c);B=sum(parts)
    out=[['.']*m for _ in range(m)]
    for i,s in enumerate(inner,4):out[i][4:-4]=s
    for i,j in M:out[i][j]='#'
    out=[''.join(s) for s in out];tree=verify(out)
    assert n>=103 and ten<=A<=16*n-164 and tree[0]==marks(inner)+B
    A=min(A,16*n-170)
    assert ten<=A
    r=optimal_four(m)
    scores=[]
    for _ in range(4):
        scores.extend(transplant(c,t) for t in (r,r[::-1]));r=tuple(map(''.join,zip(*r[::-1])))
    t,physical,nu=max(scores,key=lambda s:s[0]);assert verify(physical)[0]==marks(inner)+t
    upper=3*k*k+5*k+(k-5)//3
    # Either keep the old crop, or actually perform the refill. The
    # first bound reads no original marks between depths six and nine.
    conditional=min(R,A-max(B,t));measured=min(R,ten-max(B,t))
    j=(n-22)//3
    upper2=3*j*j+7*j-(j-5)//7-int((n-20)%42==35)
    print('side',n,'removed',R,'old ten layers',ten,'conditional cap',A,
          'wired/template refill',B,t,'cycle ranks',nu,
          'conditional / measured upper',min(upper+conditional,upper2+A),min(upper+measured,upper2+ten))
    return c,conditional,measured

def deeper_charge(rows):
    n=len(rows);m=n-12;c=[s[6:-6] for s in rows[6:-6]];res=[]
    for w in (4,5,6,7):
        inner=[s[w:-w] for s in c[w:-w]]
        parts,M=engine(('repair',w,0),c)
        P=set(M)|{(i+w,j+w) for i,s in enumerate(inner) for j,v in enumerate(s) if v=='#'}
        if w>=6:
            # Insulated four-layer optimum with two clear normal layers.
            four=optimal_four(m);Q={(i,j) for i,s in enumerate(four) for j,v in enumerate(s) if v=='#'}|{
                (i+w,j+w) for i,s in enumerate(inner) for j,v in enumerate(s) if v=='#'}
            if len(P)<len(Q):P=Q
        out=[''.join('#' if (i,j) in P else '.' for j in range(m)) for i in range(m)]
        tv=verify(out);res.append((w,marks(rows)-tv[0]))
    return res

def crosscheck():
    # Independent direct forced-graph enumeration, with and without
    # a fixed innermost word in the elbow. Include its reentrant square.
    n=8;w=2
    D=[(i,j) for i in range(4) for j in range(4) if min(i,j)<w]
    from .sparse_component_exchange import graph
    for mode,word in (('outer',set()),('inner',{(1,1),(1,2)})):
        fixed={p for p in D if (min(p)==1 if mode=='inner' else min(p)==0)}
        free=sorted(set(D)-fixed);best=-1
        form=lambda S:[''.join('#' if (i,j) in S else '.' for j in range(n)) for i in range(n)]
        for bits in range(1<<len(free)):
            S=word|{v for i,v in enumerate(free) if bits>>i&1}
            try:graph(form(S),set())
            except AssertionError:continue
            best=max(best,len(S)-(len(word) if mode=='inner' else 0))
        assert best==engine((mode,w,1),form(word))[0][0]
    print('conditional corner sweeps matched direct forced graphs for both boundary modes')

def obstruction_board(n,mixed=False,split=None):
    # Four free elbows separated by two blank slices. Between this
    # eight-layer forest and the full backing path are two blank rings.
    P=set();seeds={};L=n//2+(16 if mixed else 0) if split is None else split
    for side in range(4):
        w=10 if mixed and side in (1,2) else 8
        arms=((L,n//2),(n//2,n-L),(n-L,n-n//2),(n-n//2,L))[side]
        key=(w,arms[0]-1-w,arms[1]-1-w)
        if key not in seeds:seeds[key]=engine(('witness',*key))
        v,M=seeds[key]
        for _ in range(side):M=[(x,n-1-y) for y,x in M]
        P.update(M)
    t=n-20;holes={(0,1),(0,2),(1,t-1),(t-1,t-2),(t-2,0)}
    P.update((i+10,j+10) for i,j in set(ring(t))-holes if not mixed or j+10<L-1)
    if n==103:
        core=build(77)
        P.update((i+13,j+13) for i,row in enumerate(core) for j,s in enumerate(row) if s=='#')
    r=[''.join('#' if (i,j) in P else '.' for j in range(n)) for i in range(n)]
    if mixed:
        # Recover some of the packing seams, accepting an entire forced
        # star only when its newly incident neighbours are independent.
        from .sparse_component_exchange import graph
        F=graph(r,set())
        for d in range(10):
            for y,x in ring(n-2*d):
                p=i,j=y+d,x+d
                if p in P:continue
                nbr=[(a,b) for a,b in ((i,j-1),(i,j+1),(i-1,j),(i+1,j)) if
                     0<=a<n and 0<=b<n and (a,b) not in P]
                comp=[F.root(q) for q in (p,*nbr)]
                if len(comp)!=len(set(comp)):continue
                for q in nbr:assert F.join(p,q)
                P.add(p)
        r=[''.join('#' if (i,j) in P else '.' for j in range(n)) for i in range(n)]
    return verify(r),verify(r,True),[v for v,_ in seeds.values()]

def obstruction(n,mixed=False):
    tree,board,seeds=obstruction_board(n,mixed)
    c,_,_=charge(board);m=len(c);U=sum(engine(('inner',5,4),c)[0])
    ten=marks(board)-marks([s[10:-10] for s in board[10:-10]])
    # Upper for EVERY refill, even if all four new layer words change.
    min_loss=ten-U
    print('original tree',tree,'old elbow scores',seeds,'four-layer refill ceiling',U,
          'least possible effective loss >=',min_loss,'comb budget',comb(n)-comb(m))
    assert min_loss>comb(n)-comb(m)
    if mixed:
        assert ten+2373>3646 and 2858+min_loss>3646
        print('even exact four-layer recovery cannot pay:',2858+min_loss,
              'or higher from the crop bound; measured ten + solved inner upper',ten+2373)
        deeper=deeper_charge(board);assert dict(deeper)[6]<=788
        print('deeper wired or insulated refill: (thickness, effective loss)',deeper)

if __name__=='__main__':
    crosscheck()
    charge(locked_fringe(103))
    ordinary=construct(103,4);charge(ordinary)
    print('ordinary comb deeper costs',deeper_charge(ordinary))
    obstruction(103)
    obstruction(103,True)
