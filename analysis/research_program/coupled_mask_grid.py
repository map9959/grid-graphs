"""Emit the certified uncapped plaquette domains for the physical strip solver."""
from functools import lru_cache
from subprocess import run
from .ordered_seam_price import rowchart,table

def instance(axis,k,q,fan=False,as_tables=False):
    tabs=[];ids={}
    lo,hi=(q,q) if isinstance(q,int) else q
    assert 1<=lo<=hi<=k-2 and (not fan or lo==hi)
    top=[16]+[48]*(lo-2)+[16,4]+[6]*(k-lo-1) if fan else []
    bot=[192]*(k-2)+[128,8] if fan else []
    @lru_cache(None)
    def tid(r,j,ds,nn,ss):
        p=tuple(sorted({(a,b,c,e) for d in ds for (a,c),ys in table(axis,r,j,d).items()
                        for b,e in ys if (not nn or (a,c)==nn) and (not ss or (b,e)==ss)}))
        if p not in ids:ids[p]=len(tabs);tabs.append(p)
        return ids[p]
    grid=[]
    for y in range(k-1):
        for x in range(k-1):
            ds=range(max(-4,min(5,lo-x)),max(-4,min(5,hi-x))+1)
            grid.append(tid(rowchart(x,k),rowchart(y,k),ds,
                            tuple(top[x:x+2]) if y==0 else (),
                            tuple(bot[x:x+2]) if y==k-2 else ()))
    return (tabs,grid) if as_tables else encode(k,tabs,grid)

def encode(k,tabs,grid):
    out=[f'{k} {len(tabs)}']
    for p in tabs:
        out.append(str(len(p)));out.extend(' '.join(map(str,t)) for t in p)
    out.append(' '.join(map(str,grid)))
    return '\n'.join(out)

if __name__=='__main__':
    import sys
    axis,k=map(int,sys.argv[1:3]);q=tuple(map(int,sys.argv[3].split(':'))) if ':' in sys.argv[3] else int(sys.argv[3])
    run(['target/coupled_mask_grid',*sys.argv[4:]],input=instance(axis,k,q,'--fan' in sys.argv),
        text=True,check=True)
