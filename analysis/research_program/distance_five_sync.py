"""Synchronized square length and rooted front, with an independent DP replay."""
from subprocess import run
from .synchronous_grid import domains,unpack
from .coupled_mask_check import check
from .coupled_mask_grid import instance
from .synchronous_front import attempt
from .synchronous_front import prune
from .synchronous_grid import rectangle
from .coupled_mask_check import Pool

def root_control():
    W=17;H=9;f=7;pool=Pool()
    def tile(x,y):return (3 if y==H-1 else 7) if x>=f else 0
    grid=[pool.intern(frozenset({(tile(i,j),tile(i,j+1),tile(i+1,j),tile(i+1,j+1))}))
          for j in range(H-1) for i in range(W-1)]
    for solver in (rectangle,prune):
        assert solver(grid.copy(),pool,W,H,(),f,False)
        assert not solver(grid.copy(),pool,W,H,(),f,True)
        assert solver(grid.copy(),pool,W,H,(),W,True)
    print('planted lines: open tail accepted, two teeth rejected, south-only roots accepted')

def seed_checks(q):
    k=81
    for ax,gx,gy,block in ((1,48,8,14),(2,62,62,1)):
        ds,grid=domains(ax,k,q,gx,gy,block)
        allowed=[frozenset(map(unpack,t)) for t in ds]
        if ax==1:
            for y in range(k-1):
                for x in range(k-1):
                    # Exactly the missing axis-2 mask restriction. A
                    # repeated physical position uses the same clipped
                    # depth tag, not necessarily the same mask.
                    for b,m in enumerate(zip(*allowed[grid[y*(k-1)+x]])):
                        u,v=x+b//2,y+b%2
                        assert min(u,v,k-1-u,k-1-v)<4 or all(not(z&16 and z&40) for z in m)
        def inspect(pool,actual):
            # Every native fixed-point domain needed for the proof must
            # contain the independent checker's possible quadruples.
            seen=set()
            for p,r in zip(actual,grid):
                if (p,r) in seen:continue
                assert pool.items[p]<=allowed[r];seen.add((p,r))
        assert not check(ax,k,q,gx=(gx,),gy=(gy,),block=block,rounds=12,inspect=inspect)
    print('q',q,'axis reduction and planted seed domains verified',flush=True)

def audit():
    run(['rustc','--edition=2021','-O','src/bin/coupled_mask_grid.rs','-o','target/coupled_mask_grid'],check=True)
    root_control()
    for a in (1,2):
        data=instance(a,221,1)
        out=run(['target/coupled_mask_grid','3'],input=data,text=True,capture_output=True,check=True).stdout
        assert out.splitlines()[-1]=='EMPTY h=3 pass=0 horizontal=false start=164'
        assert check(a,221,1,data=data)
    qs=tuple(range(1,24,2))
    for q in qs:seed_checks(q)
    for native in (True,False):
        assert attempt(2,81,28,4,8,62,62,6,20,tail=True,native=native,q=qs)
    print('all synchronized terminal heights empty on both replays')
if __name__=='__main__':audit()
