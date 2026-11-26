"""All 2->3 exchanges inside a translated rail window; replay via the run ledger."""
from itertools import combinations,product
from collections import Counter
from .run_rail_swap import DIR,DIA,build
from .rail_swap_uniform import geometry,expr

def run(n,name,distributed=False,after_cap_edit=False):
    t=(n-35)//42;F=5+7*t;M=6+6*t
    # Both upper and lower components approach the merger. The other two
    # windows test the repeated drifting band and the bottom termination.
    y,x,rows,cols,aff={
        'merger':(3+F,3*F,range(-5,5),range(-10,12),'i=8+7t and j=15+21t'),
        'drift':(3+F+7,3*F-3,range(0,7),range(-7,9),'i=15+7t and j=12+21t'),
        'cap':(n-6,M,range(-7,4),range(-9,10),'i=29+42t and j=6+6t')
    }[name]
    W=set(product(rows,cols));halo=set(product(range(rows.start-2,rows.stop+2),range(cols.start-2,cols.stop+2)))
    board=build(n)
    X={(r,c) for r,c in halo if 0<=r+y<n and 0<=c+x<n and board[y+r][x+c]=='#'}
    if after_cap_edit and name=='cap':
        X.difference_update(((1,2),(3,1)));X.update(((2,0),(2,1),(2,2)))
    near=lambda u,dirs:{(u[0]+a,u[1]+b) for a,b in dirs}
    cl=lambda u:{u}|near(u,DIR)
    D={u:near(u,DIR) for u in halo}; G={u:near(u,DIA) for u in W}
    empty=W-X;valid={v for v in empty if not G[v]&X}
    freq=Counter();example={}
    profiles={}
    for rm in (s for k in (range(3) if distributed else (2,)) for s in combinations(sorted(W&X),k)):
        rem=set(rm);V=valid|{v for v in set().union(*(G[a] for a in rm))&empty if (G[v]&X)<=rem}
        need={u for u in set().union(*(cl(a) for a in rm)) if cl(u)&X<=rem}
        loss=sum(len(D[a]&X) for a in rm)-sum(a in D[b] for a,b in combinations(rm,2))
        after={v:len(D[v]&X-rem) for v in V}
        for ins in (s for k in (range(4) if distributed else (3,)) for s in combinations(sorted(V),k)):
            if any(b in G[a] for a,b in combinations(ins,2)):continue
            delta=sum(after[u] for u in ins)+sum(a in D[b] for a,b in combinations(ins,2))-loss
            if not distributed and delta!=3:continue
            I=len(need-set().union(*(cl(u) for u in ins)))
            if distributed:
                if not I:profiles.setdefault((len(rm),len(ins),delta),[]).append((rm,ins))
            else:freq[I]+=1;example.setdefault(I,(rm,ins))
    if distributed:return profiles
    return (freq,example,W,halo,X,aff,(y,x))

def audit(name):
    inside,marks=geometry()
    ct,eg,W,halo,X,aff,(y,x)=run(119,name)
    pos=expr('t>=2 and '+aff)
    for u in halo:assert (pos-marks(u) if u in X else pos&marks(u)).none(),(name,u)
    for u in W:assert (pos-inside(u)).none()
    for n in (161,203):assert run(n,name)[:2]==(ct,eg)
    print(name,'windows verified for all t>=2; score/run candidates by uncovered count',dict(sorted(ct.items())),
          'best edit',eg[min(ct)] if ct else None,flush=True)
    return ct,eg
def pools(n):
    out=[]
    for name in ('merger','drift','cap'):
        out.append(run(n,name,True))
    candidates=[]
    for a,b,c in product(*out):
        if tuple(sum(v) for v in zip(a,b,c))==(2,3,3):
            candidates.extend(product(out[0][a],out[1][b],out[2][c]))
    print('three-window allocations:',len(candidates),'pass all local ledger/coverage/diagonal checks',flush=True)
    return candidates

def physical(n,rm,ins):
    _,_,_,_,_,_,(y,x)=run(n,'cap')
    X={(i,j) for i,row in enumerate(build(n)) for j,b in enumerate(row) if b=='#'}
    Y=(X-{(r+y,c+x) for r,c in rm})|{(r+y,c+x) for r,c in ins}
    assert len(Y)==len(X)+1
    runs={};R=0
    for u in Y:
        if u in runs:continue
        todo=[u];runs[u]=R
        for i,j in todo:
            for a,b in DIR:
                v=i+a,j+b
                if v in Y and v not in runs:runs[v]=R;todo.append(v)
        R+=1
    leader=list(range(R));J=I=cyc=0
    def root(u):
        while leader[u]!=u:leader[u]=leader[leader[u]];u=leader[u]
        return u
    for i,j in product(range(n),repeat=2):
        if (i,j) in Y:continue
        ns=[runs[i+a,j+b] for a,b in DIR if (i+a,j+b) in Y]
        if not ns:I+=1
        assert len(ns)<=2
        if len(ns)==2:
            a,b=map(root,ns);J+=1
            if a==b:cyc+=1
            else:leader[a]=b
    cc=len({root(u) for u in range(R)})
    assert (R,I,J,cc,cyc)==(8*n//7-2,0,R-1,2,1)
    print(n,'(marks,runs,isolates,joins,join components,cycle rank)',(len(Y),R,I,J,cc,cyc))

if __name__=='__main__':
    for name in ('merger','drift','cap'):audit(name)
    rm=((1,2),(3,1));ins=((2,0),(2,1),(2,2))
    assert pools(119)==[(((),()),((),()),(rm,ins))]
    inside,marks=geometry()
    missing=expr('0<=i<35+42t and 0<=j<35+42t')
    for v in ((0,0),*DIR):missing=missing-marks(v)
    assert missing.none()
    # In cap-centered coordinates the two horizontal sides use
    # the new seven-mark rod and the bottom perimeter bar.
    cycle=([(2,j) for j in range(-6,5)]+[(i,4) for i in range(3,6)]+
           [(5,j) for j in range(3,-7,-1)]+[(i,-6) for i in (4,3)])
    assert len(set(cycle))==len(cycle)==26
    pos=expr('t>=2 and i=29+42t and j=6+6t')
    def occupied(v):return v in ins or (v not in rm and (pos-marks(v)).none())
    for a,b in zip(cycle,cycle[1:]+cycle[:1]):
        assert abs(a[0]-b[0])+abs(a[1]-b[1])==1 and (occupied(a) or occupied(b))
    print('uniform 26-edge forced cycle verified for every n=119+42s')
    for n in (119,161,203):physical(n,rm,ins)
