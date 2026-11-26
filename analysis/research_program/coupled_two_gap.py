"""Retest only the ordinary short-arc exits remaining at side 623."""
from functools import lru_cache
import subprocess
from .coupled_mask_grid import encode
from .two_gap_mask_tables import local,context

def keyer(k,q,halo=4,one=None):
    n=3*k+2;e=2+3*q
    if one is None:frame,parents=context(n,q)
    else:
        from .slit_star_transfer import frame_path
        frame,parents=frame_path(n,one)
    # Group boxes by their ACTUAL local physical data, not by the identity
    # of a tile chart from a different frame. Clipped single coordinates
    # determine both patch and star types (and every reflected type).
    def coord(x,S,h):
        return x if x<h else 2*h+3+x-S if x>=S-h else h+(x-h)%3
    def loc(i):return range(max(0,1+3*i-halo),min(n,1+3*i+6+halo))
    def tags(i):
        return tuple((u-(1+3*i),coord(u,n,6),coord(n-1-u,n,6),
                      coord(u,n-2,5),coord(n-3-u,n-2,5)) for u in loc(i))
    tags0=[tags(i) for i in range(k-1)]
    @lru_cache(None)
    def border(i,j):
        x=1+3*i;y=1+3*j
        ext=0 if one is None else 2
        return tuple((a-y,b-x,frame[a,b],parents.get((a,b),-2))
                     for a in range(max(0,loc(j).start-ext),min(n,loc(j).stop+ext))
                     for b in range(max(0,loc(i).start-ext),min(n,loc(i).stop+ext)) if (a,b) in frame)
    def keys(i,j):
        x=1+3*i;xs=loc(i);ys=loc(j)
        ext=0 if one is None else 2
        have_border=xs[0]<=1+ext or xs[-1]>=n-2-ext or ys[0]<=1+ext or ys[-1]>=n-2-ext
        exit_offset=e-x if 2 in ys and e in xs else None
        key=tags0[i],tags0[j],border(i,j) if have_border else (),exit_offset
        deep=tuple(min(a,b,k-1-a,k-1-b)>=4 for a in (i,i+1) for b in (j,j+1))
        return key,deep
    return keys

def instance(k,q,halo=4,drat=False,one=None,axis=1,as_tables=False):
    n=3*k+2;e=2+3*q;keys=keyer(k,q,halo,one)
    cache={};indices={};tabs=[];grid=[]
    for j in range(k-1):
        for i in range(k-1):
            key,deep=keys(i,j)
            if key not in cache:cache[key]=local(n,q,i,j,halo,drat,one)
            k0=key,deep
            if k0 not in indices:
                p=tuple(w for w in cache[key] if all(not(ok and m&16 and m&(130 if axis==1 else 40)) for ok,m in zip(deep,w)))
                indices[k0]=len(tabs);tabs.append(p)
            grid.append(indices[k0])
    print('exit' if one is None else f'one-gap frame {one} distance',e,'verified local table types',len(cache),'axis-filtered domains',len(tabs),flush=True)
    return (tabs,grid) if as_tables else encode(k,tabs,grid)

def test(q,halo=4):
    data=instance(207,q,halo)
    p=subprocess.run(['target/coupled_mask_grid','3',f'--exit={q}'],input=data,text=True,capture_output=True,check=True)
    print('exit',2+3*q,p.stdout.splitlines()[-1],flush=True)
    return p.stdout.splitlines()[-1]
if __name__=='__main__':
    import sys
    test(*map(int,sys.argv[1:]))
