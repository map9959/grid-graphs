"""Replay labelled component births/merges/payments and the all-size debit table."""
from collections import defaultdict
from itertools import product
from .component_debt import bound,contacts,west_joins
from .joined_arm_budget import layout,row,spectrum

def labels(path,start,k):
    """Transposed k-slice tile data. Sweep WEST-to-EAST, keep birth identities."""
    h=len(path[0]);X={(3*i+l//3,3*j+l%3) for j,w in enumerate(path)
                       for i,m in enumerate(w) for l in range(9) if m>>l&1}
    tooth=lambda x:x[1] in (1,3*k-2) or x[0]+3*start in (1,3*k-2)
    parent={};ground={};live={};payments={};born_at={};merged=0
    def root(x):
        while parent[x]!=x:parent[x]=parent[parent[x]];x=parent[x]
        return x
    def join(x,y):
        nonlocal merged
        p,q=root(x),root(y)
        assert p!=q and not(ground[p] and ground[q])
        merged+=bool(live[p] and live[q])
        parent[p]=q;ground[q]|=ground.pop(p)
        live[q].update(live.pop(p))
        if ground[q]:
            for label in live[q]:payments[label]=(i,ground[q])
            live[q].clear()
    prev_u=prev_pot=0
    for i in range(h):
        nodes={x for x in X if x[0]//3==i}
        for x in nodes:
            parent[x]=x;ground[x]={x} if tooth(x) else set();live[x]=set()
        joins=[]
        for x in nodes:
            for di,dj in ((-1,0),(0,-1)):
                y=(x[0]+di,x[1]+dj)
                if y not in X:y=y[0]+di,y[1]+dj
                if y not in X:continue
                if y in nodes:join(x,y)
                else:joins.append((x,y))
        roots={root(x) for x in nodes}
        touched={root(x) for x,y in joins}
        births=[p for p in roots-touched if not ground[p]]
        count=sum(not ground[p] for p in roots)
        # Use any fixed ordering of new birth labels at a column. Price
        # the first at two and subsequent ones at six for this replay.
        for j,p in enumerate(sorted(births)):
            born_at[p]=(i,2 if j==0 else 6);live[p].add(p)
        for x,y in joins:join(x,y)
        u=sum(not v for v in ground.values())
        owed=sum(born_at[label][1] for ls in live.values() for label in ls)
        paid=sum(born_at[label][1] for label,(end,_) in payments.items() if end==i)
        assert u-prev_u==count-len(joins)
        assert paid+(owed-u)-prev_pot==sum(born_at[p][1] for p in births)-(u-prev_u)
        prev_u=u;prev_pot=owed-u
        if 0<i<h-1:
            # Independent transfer counts vs the physical component graph.
            state=-1,(0,1,2),(0,0,0);finished=[];edges=0
            ref=7 if 7<=start+i<=k-8 else start+i if start+i<7 else start+i-k+39
            for j,w in enumerate(path):
                strip=w[i-1:i+2];edges+=west_joins(strip)
                state,ds=contacts(state,strip,j in (0,k-1),ref)
                finished.extend(ds)
            finished.extend(v for v in state[2] if v&1)
            assert edges==len(joins) and finished.count(5)==len(births)
            assert sum(not(v&8) for v in finished)==count
    assert prev_u==prev_pot==0 and born_at.keys()==payments.keys()
    # Verify each recorded payee is the actual tooth of that final tree.
    assert all(target==ground[root(p)] and len(target)==1 for p,(_,target) in payments.items())
    return len(born_at),merged,max((end-born_at[p][0] for p,(end,_) in payments.items()),default=0)

def replay_region():
    # Two pending arms meet in column two; only in column three does
    # their common path reach a tooth. This tests that a merger does not
    # discharge either label prematurely (a graph regression, not a tile witness).
    X={(x,y) for x in (0,2,4,6) for y in (10,18)}|{
        (6,12),(6,14),(6,16),(8,14),*((10,y) for y in (14,12,10,8,6,4,2,1))}
    p=[tuple(sum(1<<b for b in range(9) if (3*i+b//3,3*j+b%3) in X)
             for i in range(4)) for j in range(39)]
    assert labels(p,7,39)==(2,1,3)
    print('two-label physical merge: both paid at the tooth after 3 columns')
    # Reconstruct a known fully rooted region, not a full-board construction.
    for t in (0,3):
        k,H,_=layout(t);s=k-4*H//3
        bs,get=spectrum(7,4,1,True,0,True,s,True)
        p=get((bs&-bs).bit_length()-1);j=s+4
        p=p[:j+1]+[p[j]]*(14*t)+p[j+1:]
        east=zip(*(row(k,q)[1] for q in reversed(range(H))))
        united=[(*a,*b) for a,b in zip(p,east)]
        print('regional label replay: births, mergers of labelled classes, max delay',
              labels(united,k-H-4,k),flush=True)

F={
    (1,2):[9,9,7,5,6,6,6,6,6,6,6,6,7,14,11],
    (1,6):[9,9,-17,-19,-10,2,2,2,2,2,2,-16,-16,9,11],
    (2,2):[9,9,7,5,5,5,5,5,5,5,5,6,7,14,11],
    (2,6):[9,9,-17,-19,-19,-19,-19,-19,-19,-19,-19,-18,-16,9,11]}
def check():
    replay_region()
    for axis,price in product((1,2),(2,6)):
        v=[bound(axis,price,r) for r in (*range(8),*range(32,39))]
        assert v==F[axis,price]
        east=bound(axis,price,phase=-4)
        arm=[bound(axis,price,long=j) for j in range(3)]
        assert (east,arm)==((9,[16]*3) if price==2 else (5,[12]*3))
        print('axis',axis,'price',price,'fringe/bulk table',v,'east',east,'arm',arm[0],flush=True)
    for axis in (1,2):
        tab=F[axis,2]
        fringe=(*range(8),*range(32,39))
        ceiling=[-bound(axis,0,r,traffic=4 if r in (0,38) else 2 if r in (1,37) else 3)
                 for r in fringe]
        assert ceiling==[4]*14+[6] and bound(axis,0,phase=-4,traffic=3)==-3
        assert bound(axis,2,phase=-4,rate=-1)==9
        assert all(bound(axis,2,long=j,rate=-1)==16 for j in range(3))
        for t in (0,1):
            k=39+14*t;baseline=sum(tab)+(k-15)*tab[7]
            assert 3*(198+72*t)-baseline==((340+132*t) if axis==1 else (371+146*t))
            assert 198+72*t-(sum(ceiling)+(k-15)*ceiling[7])==40+16*t
    print('whole-square headroom at base prices: 340+132t / 371+146t')
    print('necessary excess seam traffic: 6*sum(max(J-1,0)) >= 40+16t + east bulk count')
    # An arithmetic control, not geometric data: keep a live rootless tree
    # through many cuts, absorb a second birth on alternating steps, and
    # pay every label at a single later tooth. The summed bills alone
    # admit the equality budget.
    for t in (0,1,12):
        k=39+14*t;ds=[5+(i<3+2*t) for i in range(k)]
        u=births=0
        for i in range(k):
            old=u;b=0
            if i==7 or (8<=i<k-9 and i%2==0):b=1;u+=1
            elif u==2:u=1
            elif i==k-8:u=0
            births+=b
            if 7<=i<=k-8:L,S=9,4
            else:
                j=i if i<7 else i-k+15
                L=F[2,2][j];S=L-F[2,6][j]
            toll=max(0,4*b-S,2*(u-old) if 7<=i<=k-8 else 0)
            local=ds[max(0,i-1)]+ds[i]+ds[min(k-1,i+1)]
            assert local+u-old>=L+2*b+toll
            # Four joins per interior seam: abstract count control only.
            assert ds[i]<=((3 if 7<=i<=k-8 else 6 if i==k-1 else 4)
                           +u-old+3*int(i>0)+3*int(i<k-1))
        assert u==0 and sum(ds)==198+72*t
        print('scalar control k',k,'labels paid',births,'deficit',sum(ds))
if __name__=='__main__':check()
