"""Charge off-perimeter stars to vacancies when peeling three-layer collars."""
from .wired_crop_exchange import ring
from .end_band_obstruction import wrapped
from .extend_forest_28 import verify
from .comb_cap_transfer import construct
from .sparse_component_exchange import graph

def comb(n):
    k=n//3
    return 3*k*k+5*k+(3*k-13)//10

def price(rows,t):
    n=len(rows);m=n-6*t
    assert n%3==1 and m>=10 and t>=1
    M={(i,j) for i,s in enumerate(rows) for j,c in enumerate(s) if c=='#'}
    shell={v for v in M if min(*v,n-1-v[0],n-1-v[1])<3*t}
    handled=set();budget=0;ledger=[]
    for h in range(0,3*t,3):
        s=n-2*h
        R=[(y+h,x+h) for y,x in ring(s)]
        holes=set(R)-M;loads={v:0 for v in holes}
        handled.update(set(R)&M);guards=set()
        for i,v in enumerate(R):
            a,b=R[i-1],R[(i+1)%len(R)]
            if v not in M or not (a in holes and b in holes):continue
            dy,dx=v[0]-a[0],v[1]-a[1]
            if (dy,dx)!=(b[0]-v[0],b[1]-v[1]):continue
            for sign in (1,-1):
                g=v[0]+sign*dx,v[1]-sign*dy
                if g in shell and g not in handled:
                    guards.add(g);handled.add(g);loads[a]+=1;loads[b]+=1
        cap=1 if h==0 else 2
        assert all(v<=cap for v in loads.values())
        unused=sum(v==0 for v in loads.values())
        # Ignore all finer load data; only use the number of untouched holes.
        credit=len(holes)-(cap*(len(holes)-unused))//2
        budget+=credit
        ledger.append((len(holes),len(guards),unused,credit))
    stray=len(shell-handled);delta=comb(n)-comb(m)
    perimeter=sum(4*(n-6*j)-4 for j in range(t))
    saving=delta-perimeter+budget-stray
    assert len(shell)<=delta-saving
    crop=[s[3*t:n-3*t] for s in rows[3*t:n-3*t]]
    return ledger,stray,saving,len(shell),crop

def shadows(rows,t,crop,with_sources=False):
    """Recover inner-fringe marks in the crop, using its unrestricted components."""
    h=3*t;m=len(crop);cand=set();source={}
    for i in range(m):
        for z,v in (((h-1,h+i),(0,i)),((h+m,h+i),(m-1,i)),
                    ((h+i,h-1),(i,0)),((h+i,h+m),(i,m-1))):
            if rows[z[0]][z[1]]=='#' and crop[v[0]][v[1]]=='.':
                cand.add(v);source.setdefault(v,[]).append(z)
    # A spanning forest of the union of all proposed stars witnesses
    # a simultaneous solution: discard owners of every rejected edge.
    # For adjacent shadows an edge can have two owners, so record both.
    owners={}
    for y,x in cand:
        for u,v in ((y-1,x),(y+1,x),(y,x-1),(y,x+1)):
            if 0<=u<m and 0<=v<m and crop[u][v]=='.':
                edge=tuple(sorted(((y,x),(u,v))))
                owners.setdefault(edge,set()).add((y,x))
    F=graph(crop,set());bad=set();cycles=0
    for (p,q),donors in sorted(owners.items(),key=lambda kv:(-len(kv[1]),kv[0])):
        if not F.join(p,q):cycles+=1;bad.update(donors)
    keep=cand-bad
    out=list(map(list,crop))
    for y,x in keep:out[y][x]='#'
    result=len(cand),cycles,len(keep),[''.join(s) for s in out]
    return (result,{source[v][0] for v in keep}) if with_sources else result

def fringe_test(n):
    r=list(map(list,wrapped(n)))
    # Break the next ring along one side. Independent inward teeth on
    # the outer path can now occupy the last layer of the peeled collar.
    for j in range(8,n-8):r[3][j]='.'
    for j in range(11,n-11,3):r[2][j]='#'
    rows=[''.join(s) for s in r];v=verify(rows)
    _,X,S,removed,crop=price(rows,1)
    q,beta,A,new=shadows(rows,1,crop);v1=verify(new)
    delta=comb(n)-comb(n-6)
    assert removed>delta and S+A>=1 and v[0]-v1[0]==removed-A
    print('recoverable fringe',n,'raw removal',removed,'budget',delta,
          'strays/shadows/rank excess/kept',(X,q,beta,A),'net saving',S+A,
          'marked trees',v,v1)

def peel(rows):
    """One step without a reference perimeter word, using the two-ring cap."""
    n=len(rows);m=n-6
    crop=[s[3:-3] for s in rows[3:-3]]
    q,beta,A,new=shadows(rows,1,crop)
    ann=sum(rows[i+h][j+h]=='#' for h in (0,1) for i,j in ring(n-2*h))
    f=sum(rows[i+2][j+2]=='#' for i,j in ring(n-4))
    assert ann<=4*n-9
    e=comb(n)-comb(m)-(4*n-6)
    assert e in (0,1)
    saving=3+e-(f-A)
    assert sum(s.count('#') for s in rows)-sum(s.count('#') for s in new)<=comb(n)-comb(m)-saving
    return new,(f,q,beta,A,saving)

def four_layer_peel(rows):
    n=len(rows);m=n-12
    crop=[s[6:-6] for s in rows[6:-6]]
    q,beta,A,new=shadows(rows,2,crop)
    counts=[sum(rows[h+i][h+j]=='#' for i,j in ring(n-2*h)) for h in range(6)]
    candidates=[]
    for d in range(3):
        cap=8*(n-2*d)-40
        assert sum(counts[d:d+4])<=cap
        other=sum(counts[:d]+counts[d+4:])
        candidates.append(comb(n)-comb(m)-cap-other+A)
    assert sum(counts)-A<=comb(n)-comb(m)-max(candidates)
    return new,(counts,A,candidates)

def guarded(n):
    m=n-6;core=construct(m,4)
    M={(i+3,j+3) for i,s in enumerate(core) for j,c in enumerate(s) if c=='#'}
    R=set(ring(n))-{(0,1),(0,2),(1,n-1),(n-1,n-2),(n-2,0)}
    for x in range(9,n-9,7):
        R-={(0,x-1),(0,x+1),(0,x+2)}
        M.add((1,x))
    M|=R
    return [''.join('#' if (i,j) in M else '.' for j in range(n)) for i in range(n)]

def audit():
    for rows,t in ((wrapped(103),5),(guarded(103),1)):
        n=len(rows);m=n-6*t;start=verify(rows)
        L,X,S,removed,crop=price(rows,t);finish=verify(crop)
        k=m//3;upper=3*k*k+5*k+(k-5)//3
        assert start[0]-finish[0]==removed and S>=upper-comb(m)
        print('crop',n,m,'(holes,assigned,untouched,credit)',L,'unassigned',X,
              'removed/delta',removed,comb(n)-comb(m),'certified saving',S,
              'transferred upper',upper+comb(n)-comb(m)-S,'trees',start,finish)
    fringe_test(103)
    r=wrapped(103);total=0
    for _ in range(5):
        r,stats=peel(r);total+=stats[-1]
    assert total==18;print('five successive word-free steps: saving',total,'crop tree',verify(r))
    r,stats=peel(construct(103,4));print('comb control (fringe,candidates,cycle excess,kept,saving)',stats,'crop tree',verify(r))
    rows=list(map(list,wrapped(103)))
    for x in range(12,91):rows[6][x]='.'
    for x in range(15,88,3):rows[5][x]='#'
    rows=[''.join(s) for s in rows]
    v=verify(rows);r,(counts,A,S)=four_layer_peel(rows);v1=verify(r)
    assert A==25 and max(S)==5 and v[0]-v1[0]==sum(counts)-A
    print('four-layer cap + shadows',counts,'recovered',A,'saving',max(S),
          'upper from side 91',2858+comb(103)-comb(91)-max(S),'trees',v,v1)
if __name__=='__main__':audit()
