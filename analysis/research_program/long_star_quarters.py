"""Does every intact long realization induce a forbidden 203 three-quarter realization?"""
from itertools import product
from pathlib import Path
import gzip,sys
from .defect_window import table
from .shorten_245_star import audit
from .slit_star_transfer import frame_path
from .depth_two_far_quarter import run
from .depth_two_203_ledger import FAR,checked
from collections import deque

def fringe(n,B,X,star,tab):
    """Try to complete the frozen marks by forced single-bit implications."""
    T,P,_=tab
    known={u:int(u in X) for u in B};todo=deque(sorted(known))
    def fix(p,b):
        if p in known:return known[p]==b
        known[p]=b;todo.append(p);return True
    steps=0
    while todo:
        i,j=todo.popleft();steps+=1
        if known[i,j]:
            for a,b in product((-1,1),repeat=2):
                p=i+a,j+b
                if 0<=min(p) and max(p)<n and not fix(p,0):return 'diagonal',(i,j),p,steps
        for a,b in ((0,0),(1,0),(0,1),(-1,0),(0,-1)):
            p=i+a,j+b
            if min(p)<0 or max(p)>=n or p==star:continue
            cross=[(p[0]+c,p[1]+d) for c,d in ((0,0),(1,0),(0,1),(-1,0),(0,-1))]
            possible=[q for q in cross if min(q)>=0 and max(q)<n and known.get(q,1)]
            if not possible:return 'uncovered',p,None,steps
            if len(possible)==1:fix(possible[0],1)
        # On a fully fixed exterior patch the ordinary replay checked
        # its charge. Only propagate patches meeting the unfilled region.
        for a,b in product(range(3),repeat=2):
            r,c=i-a,j-b
            if min(r,c)<0 or max(r,c)>n-3:continue
            if r+2<102 or r>n-9 or c+2<8 or c>=n-102:continue
            sq=[(r+h,c+k) for h,k in product(range(3),repeat=2)]
            must=sum(1<<k for k,q in enumerate(sq) if known.get(q)==1)
            zero=sum(1<<k for k,q in enumerate(sq) if known.get(q)==0)
            yes=511;anymark=0;found=False
            for m,charge in enumerate(P(T(1,r,c))):
                if charge or m&zero or (m&must)!=must:continue
                found=True;yes&=m;anymark|=m
            if not found:return 'no zero-charge patch',(r,c),(must,zero),steps
            for k,q in enumerate(sq):
                if yes>>k&1:fix(q,1)
                if not anymark>>k&1:fix(q,0)
    return 'no local contradiction',len(known),None,steps

def test(lo,hi,seconds):
    ns=203;n=245
    def region(N):
        return {(i,j) for i,j in product(range(N),repeat=2) if min(i,j,N-1-i,N-1-j)<8 or i<=101 or j>=N-102}
    A=region(ns);B=region(n)
    # Insert strictly within the SW half ranges. Both transverse band
    # widths remain 102, so no extra quadrant depth is assumed.
    cuts=lambda d:(150,100 if d<=95 else 12)
    def short(d):return d if d<=95 else d-42
    sites=list(range(lo,hi+1,6));assert sites and lo%6==hi%6==5 and 5<=lo<=hi<=239
    for y,x in set(map(cuts,sites)):
        lift=lambda u:(u[0]+42*(u[0]>=y),u[1]+42*(u[1]>=x))
        assert {lift(u) for u in A}=={u for u in B if not(y<=u[0]<y+42 or x<=u[1]<x+42)}
        for d in sites:
            if cuts(d)==(y,x):
                for a,b in product(range(-2,3),repeat=2):
                    assert lift((2+a,short(d)+b))==(2+a,d+b)
    for a,b,h in FAR:
        if any(a<=short(d)<=b for d in sites):checked(f'depth_two_far_quarter_203_{a}_{b}',h)
    archive=Path(__file__).with_name('one_gap_projection_examples')/f'long_quarters_{lo}_{hi}.gz'
    def replay(w,star,X,out):
        tab=table(n);v,e,cc=audit(n,B,X,out,star,None,tab,frame_path(n,w),(244,244))
        d=star[1];assert d in sites
        if seconds==-1 and (lo,hi,w,d)==(5,5,11,5):
            cross={(102,7),(101,7),(103,7),(102,6),(102,8)}
            assert not cross&X and cross-B=={(102,8)} and (101,9) in X
        print('intact donor SAT; original',('west' if w>=8 else 'north'),d,'frame index',w%8,
              '-> forbidden 203 distance',short(d),'vertices',v,'edges',e,'components',len(set(cc.values())),flush=True)
        # Exhaust all Cartesian cuts, not just the two chosen for the
        # geometric inclusion above. The unfilled region is a Cartesian
        # product. Each old hole axis has length 93, the new one 135:
        # inclusion of the desired old domain forces equality on both axes.
        def starts(a,b,c,e):
            return [s for s in range(204) if {j for j in range(203) if c<=j+42*(j>=s)<=e}==set(range(a,b+1))]
        ys=starts(102,194,102,236);xs=starts(8,100,8,142)
        assert ys==list(range(102,196)) and xs==list(range(8,102))
        diagonals=[];repairs=[]
        for y in ys:
            # These columns lie to the right of EVERY vertical removal,
            # hence the unit-square obstructions survive any x choice.
            E=[(j,k) for j in range(143,245) for k in (j-1,j+1) if 143<=k<245 and (y-1,j) in X and (y+42,k) in X]
            diagonals.append(len(E))
            # A greedy matching already bounds how many distinct marked
            # endpoints must be changed before all these cycles can vanish.
            l=set();r=set()
            for j,k in E:
                if j not in l and k not in r:l.add(j);r.add(k)
            repairs.append(len(l))
        print('all',len(xs)*len(ys),'shape-preserving literal cuts; horizontal seam diagonal pairs',
              (min(diagonals),max(diagonals)),'minimum disjoint pairs',min(repairs),flush=True)
        print('completion of frozen donor into SW hole:',fringe(n,B,X,star,tab),flush=True)
        if not archive.exists():
            raw=bytes([w,d])+bytes(5*int(u in X)+out.get(u,-1)+1 for u in sorted(B))
            archive.write_bytes(gzip.compress(raw,mtime=0))
    print('intact three-quarter + rim domain',len(B),'->',len(A),'test',sites,flush=True)
    if seconds==-1:
        raw=gzip.decompress(archive.read_bytes());data=dict(zip(sorted(B),raw[2:],strict=True))
        replay(raw[0],(2,raw[1]),{u for u,b in data.items() if b>=5},{u:b%5-1 for u,b in data.items() if b%5})
    else:run(n,lo,hi,seconds,domain=B,output=f'target/long_star_quarters_{lo}_{hi}',replay=replay)
if __name__=='__main__':test(*map(int,sys.argv[1:]))
