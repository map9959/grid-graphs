"""A shrinking north fan, allowing independent padding in each constant run."""
from .synchronous_front import Pool,cell,rowchart,rectangle,prune
from .synchronous_grid import solve,unpack
from .coupled_mask_grid import instance
from .coupled_mask_check import check

def fan(a,c,r):
    assert min(a,c,r)>=0
    return [448]*a+[384,264,24]+[56]*c+[24,12,6]+[7]*r

def seed(q):
    K=81;gx=(28,68) if q in (56,57) else (28,)
    z=solve(instance(1,K,q),['--gy=60','--gx='+','.join(map(str,gx))])
    assert z is not None
    ds,g=z
    def inspect(ds,g):
        for y in range(8):
            for x in range(q+1,K-1):
                expect=6 if y==0 else 7
                assert all(p[0]==p[2]==expect for p in ds[g[y*(K-1)+x]])
        north=[16]+[48]*(q-2)+[16,4]+[6]*(K-q-1)
        for x in range(K-1):
            assert all(p[0]==north[x] and p[2]==north[x+1] for p in ds[g[x]])
        for y in range(1,9):
            a,c=3*y-2,q-6*y-2;r=K-a-c-6
            words=fan(a,c,r)
            for i in gx:assert words[i]==words[i+1]==(56 if i==28 else 7)
            for x in range(K-1):
                assert all(p[0]==words[x] and p[2]==words[x+1] for p in ds[g[y*(K-1)+x]])
    inspect([list(map(unpack,d)) for d in ds],g)
    assert not check(1,K,q,gx=gx,gy=(60,),rounds=12,inspect=lambda p,g:inspect(p.items,g))

def slab(c,step,test):
    # Coordinates are already deep. Both swept ends are open; no
    # synthetic north roots. The west/east sides remain physical.
    a=r=16;W=a+6+c+r;H=13;P=Pool();grid=[]
    rows=[fan(a+3*j,c-6*j,r+3*j) for j in range(3 if step else 2)]
    for j in range(H-1):
        for i in range(W-1):
            d=cell(1,rowchart(i,W),7,-4)
            if j==0:d=d&{(rows[0][i],rows[1][i],rows[0][i+1],rows[1][i+1])}
            grid.append(P.intern(d))
    gaps=(8,a+3+8,W-9) if step else (8,W-9)
    if step:
        for x in gaps:assert all(row[x]==row[x+1] for row in rows)
    live=test(grid,P,W,H,gaps,W,False)
    if step:
        assert live
        for x in range(W-1):
            assert all(p[1]==rows[2][x] and p[3]==rows[2][x+1] for p in P.items[grid[W-1+x]])
    else:assert not live

def audit():
    for test in (rectangle,prune):
        slab(20,True,test)
        for c in (14,16,18):slab(c,False,test)
        print(test.__name__,': fan advances (3,-6,3); terminal center lengths 14,16,18 empty',flush=True)
    for q in (56,*range(58,80,2)):seed(q)
    print('every even q>=58 covered by verified north fan')
if __name__=='__main__':audit()
