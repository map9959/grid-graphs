"""Share the exact gap count and one sector budget between the four rim ends."""
from .rim_gap_corners import data,generate,Path,run,product
from pysat.formula import IDPool
from pysat.card import CardEnc

def verify(f,tag):
    p=Path('target/sector_gap_cover');p.mkdir(exist_ok=True)
    cnf=p/(tag+'.cnf');drat=p/(tag+'.drat');f.to_file(str(cnf))
    res=run(['target/cadical/build/cadical','-t','40',str(cnf),str(drat)],capture_output=True)
    if res.returncode==20:
        out=run(['target/drat-trim/drat-trim',str(cnf),str(drat)],capture_output=True,check=True)
        assert b's VERIFIED' in out.stdout
    print(tag,{20:'s VERIFIED',10:'SAT',0:'UNKNOWN'}.get(res.returncode,'UNKNOWN'),flush=True)
    cnf.unlink();drat.unlink(missing_ok=True);return res.returncode==20

def gaps(f,X,edges,n,minimum):
    pool=IDPool(start_from=f.nv+1);bits=[]
    for (i,j),(u,v) in edges:
        b=pool.id();f.extend([[-b,-X[i*n+j]],[-b,-X[u*n+v]]]);bits.append(b)
    f.extend(CardEnc.atleast(bits,minimum,vpool=pool).clauses)

def audit(n,g):
    k=n//3;t=3*k*k+(16*k-7)//3;tables=data(n,t);p=22
    f,X=generate(n,t,set(product(range(5),range(32,44))),False,tables)
    gaps(f,X,[((0,j),(0,j+1)) for j in range(36,39)],n,1)
    if not verify(f,f'flat{n}_{g}'):return
    # Every other gap is within 20 of a corner. The translated flat
    # strip's two diagonal tags are saturated in all eight D4 images.
    from .patch_square import trans
    pos=tables[0]
    for j in range(p,n-1-p):
        h=36+(j-36)%3
        for i,c in product(range(5),range(32,44)):
            for tag in (0,1):
                assert pos(i,c,tag)==pos(i,c+j-h,tag)
    D=set();edges=[]
    for s in range(4):
        for i,j in product(range(p+4),repeat=2):D.add(trans(i,j,n,s))
        for j in range(p):
            for u,v in [((0,j),(0,j+1)),((j,0),(j+1,0))]:
                edges.append((trans(*u,n,s),trans(*v,n,s)))
    f,X=generate(n,t,D,False,tables);gaps(f,X,edges,n,g)
    verify(f,f'four{n}_{g}')
if __name__=='__main__':
    import sys
    g=int(next(z.split('=')[1] for z in sys.argv if z.startswith('--rim-gaps=')))
    for n in (103,112):audit(n,g)
