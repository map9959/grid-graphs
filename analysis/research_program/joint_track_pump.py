"""Test root colors and dual area on the same intermediate bulk words."""
from itertools import product
from array import array
from .tile_circulation import enumerate_blocks
from .colored_bulk_pump import edges
from .dual_area_pump import graph
import sys

def run(axis,colors):
    B=enumerate_blocks(0);ids={};src=[array('I'),array('I')];dst=[array('I'),array('I')]
    for w in B:
        A=edges([w],axis,colors)
        if not A:continue
        for phase in (0,1):
            D=graph([w],phase,axis)
            for (a,b),(c,d) in product(A,D):
                u=(*a,c[-1]);v=(*b,d[-1])
                src[phase].append(ids.setdefault(u,len(ids)));dst[phase].append(ids.setdefault(v,len(ids)))
    def rep(u):
        a,b,root,dual=u;rename={};shift=(colors-1).bit_length()
        mm=[h*3+k for h in range(6) for k in range(3) if (a if h<3 else b)>>(3*(h%3)+k)&1]
        h=sum(rename.setdefault(root>>(shift*k)&(colors-1),len(rename))<<(shift*k) for k in mm)
        return (a,b,h,dual if not dual&1 else dual^1023)
    canonical={rep(u) for u in ids};assert canonical<=ids.keys()
    roots=[ids[u] for u in sorted(canonical)]
    print('joint states',len(ids),'entrance orbits',len(roots),'arcs per phase',list(map(len,src)),flush=True)
    # Computing the full square of the relation would be wasteful: each
    # vertex instead holds a bitset of canonical entrances that reach it.
    for phase in (0,1):
        ans=0
        for start in range(0,len(roots),1024):
            cur=[0]*len(ids)
            for j,z in enumerate(roots[start:start+1024]):cur[z]=1<<j
            hist=[cur]
            for t in range(1,65):
                g=(phase+t-1)%2;new=[0]*len(ids)
                for u,v in zip(src[g],dst[g]):new[v]|=cur[u]
                if t>=14 and new==hist[t%14]:ans=max(ans,t-14);break
                if len(hist)<14:hist.append(new)
                else:hist[t%14]=new
                cur=new
            else:raise AssertionError('no repeat checked')
        print('axis',axis,'root colors',colors,'and dual parity; initial parity',phase,'14-step shortening from',ans,flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
