"""Locate the checked 329 two-gap core in physical coordinates."""
from collections import Counter
from inspect import getclosurevars
from pathlib import Path
from .defect_window import table,window

class Discard:
    nv=0
    def append(self,c):pass
    def extend(self,cs):pass

def run(n=329,inspect_core=None):
    assert n in (329,371,413)
    ids=set()
    p=Path(f'target/two_gap_{n}_0011_axis_ordinary'+('_linked' if n==371 else '')+'.core')
    if n==413:p=Path('target/core371_lift/halo_1_primal.core')
    with p.open() as fd:
        for line in fd:
            if not line.startswith(('p','c')):ids.update(abs(int(x)) for x in line.split()[:-1])
    def read(f,bit,flags):
        vp=getclosurevars(bit).nonlocals['vp']
        kinds=Counter();sites={}
        base=vp.top
        last=base+2+2*len(range(14,n-14,3))
        for z in ids:
            tag=vp.obj(z) if z<=base else None
            if isinstance(tag,tuple):
                k=tag[0];u=tag[1:3]
            elif z>last:
                k='color';i,j=divmod((z-last-1)//2,n-4);u=i+2,j+2
            else:k='global';u=None
            kinds[k]+=1
            if u:sites.setdefault(k,set()).add(u)
        assert last+2*(n-4)**2=={329:1724167,371:2190757,413:2716317}[n]
        if inspect_core:inspect_core(vp,base,last,ids,p)
        print('core IDs',dict(kinds))
        for k,ps in sorted(sites.items()):
            print(k,'deepest',max(min(i,j,n-1-i,n-1-j) for i,j in ps),'box',
                  min(i for i,j in ps),max(i for i,j in ps),min(j for i,j in ps),max(j for i,j in ps))
        ps=set.union(*sites.values())
        for axis in range(2):
            candidates=[]
            for c in range(12,n-13):
                lane={u[1-axis] for u in ps if abs(u[axis]-c)<=1}
                candidates.append((max([min(t,n-1-t) for t in lane],default=-1),len(lane),c))
            print('axis',axis,'shallowest cut (depth,occupied lanes,position)',min(candidates))
    sites={('s',0,d) for d in range(107,n-107,3)} if n>=371 else None
    window(n,'rim',n,table(n),matching=True,exit_only=True,emit=read,clause_sink=Discard(),defects=sites)
if __name__=='__main__':
    import sys
    run(*map(int,sys.argv[1:]))
