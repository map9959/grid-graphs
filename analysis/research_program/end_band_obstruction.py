"""Five separated perimeter paths: a rank obstruction in both orientations."""
from .end_band_rank import refill,combine,construct,verify
from .wired_crop_exchange import ring

def wrapped(n):
    m=n-30
    core=construct(m,4);marks={(i+15,j+15) for i,row in enumerate(core) for j,v in enumerate(row) if v=='#'}
    for t in range(0,15,3):
        h=n-2*t
        rim=set(ring(h))-{(0,1),(0,2),(1,h-1),(h-1,h-2),(h-2,0)}
        marks.update((t+i,t+j) for i,j in rim)
    return [''.join('#' if (y,x) in marks else '.' for x in range(n)) for y in range(n)]

def check(n):
    rows=wrapped(n);k=n//3;C=3*k*k+5*k+(3*k-13)//10
    tree=verify(rows);assert tree[0]==C-18
    vals=[]
    for board in (rows,list(zip(*rows))):
        best=None
        for a in range(1,10):
            for b in range(n-10,n-1):
                out,er=refill(board,[a,b],0,n-1,range(0,n,3))
                if best is None or best[0]<er[-1]:best=er[-1],a,b,er,out
        gain,a,b,er,out=best
        t=verify(out);assert t[0]==tree[0]+gain
        vals.append(gain)
        print('best of 81 full-width cuts',a,b,er,'tree',t,flush=True)
    sr,er,t,ub=combine(rows,8,n-9)
    print('starting tree',tree,'comb',C,'full width best gain',max(vals),
          'three-column side + end gains',sr[5],er[-1],'combined upper',ub,flush=True)
    assert max(vals)<0 and ub>C
if __name__=='__main__':check(103)
