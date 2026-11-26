"""All-size switch from axis 1 to the double-filtered bulk after an odd fan."""
from .north_fan_sync import fan,seed,slab,prune,rectangle,Pool,cell,rowchart,unpack
from .synchronous_grid import solve
from .coupled_mask_grid import encode
STRAIGHT={3,6,7,8,12,16,32,33,96,192,264,384,448}

def template(a,c,r,H):
    W=a+c+r+6;P=Pool()
    rows=[fan(a+3*j,c-6*j,r+3*j) for j in range(2)]
    gd=[]
    for j in range(H-1):
        for i in range(W-1):
            d=cell(1,rowchart(i,W),rowchart(14+j,H+14),-4)
            if not j:d=d&{(rows[0][i],rows[1][i],rows[0][i+1],rows[1][i+1])}
            gd.append(P.intern(d))
    gaps=(8,W-11)
    assert all(row[x]==row[x+1]==row[x+2] for row in rows for x in gaps)
    ds,g=solve(encode(W,P.items,gd),['--height='+str(H),'--root-from='+str(W),
             '--gx='+','.join(map(str,gaps)),'--gy=18','--block=2','--period=2'])
    allowed=[frozenset(map(unpack,t)) for t in ds]
    replay=gd.copy()
    assert prune(replay,P,W,H,gaps,W,True,ygaps=(18,),block=2)
    for i,j in set(zip(replay,g)):assert P.items[i]<=allowed[j]
    bad=[[any(m&16 and m&40 for m in ms) for ms in zip(*map(unpack,t))] for t in ds]
    for j in range(6):
        for i in range(a+c+6,W-1):
            assert all(unpack(t)==(7,7,7,7) for t in ds[g[j*(W-1)+i]])
    for j in range(5,H-1):
        for i in range(W-1):
            for b,violate in enumerate(bad[g[j*(W-1)+i]]):
                x,y=i+b//2,j+b%2
                if y>=6 and min(x,W-1-x,H-1-y)>=4:assert not violate,(a,c,r,H,x,y)
    for j in range(6,H-7):
        for i in range(6,W-7):
            assert all(set(unpack(t))<=STRAIGHT for t in ds[g[j*(W-1)+i]])

def audit():
    for q in range(57,80,2):seed(q)
    for test in (rectangle,prune):slab(19,True,test)
    for c in (13,15,17):
        for a in (16,17):
            for r in (16,17):
                for H in (39,40):template(a,c,r,H)
        print('center length',c,'all padding parities give axis 2 below row 6',flush=True)
if __name__=='__main__':audit()
