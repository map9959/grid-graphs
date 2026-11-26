"""All-length coupled-strip tests. No physical cut count is truncated."""
import sys
from subprocess import run
from .coupled_mask_grid import instance,encode
from .coupled_mask_check import check
from .coupled_two_gap import instance as bridge,keyer
from .two_gap_mask_tables import VERIFIED
from .ordered_ports import typ

def native(data,gx,gy,*,q=None,extra=()):
    opts=[f'--{s}='+','.join(map(str,g)) for s,g in (('gx',gx),('gy',gy)) if g]
    if q is not None:opts.append(f'--exit={q}')
    output=run(['target/coupled_mask_grid','3',*opts,*extra],input=data,text=True,
               capture_output=True,check=True).stdout.splitlines()
    return output[-1]

def fold(i,gaps):
    for g,n in reversed(gaps):
        i=i if i<g else max(g,i-n)
    return i

def bridge_tags(q0,a,b):
    """Check local physical charges, frame/parents, exit offset and deep-axis guards."""
    base=207;k=base+a+b
    f=keyer(base,q0);g=keyer(k,q0+a)
    # Undo insertions in reverse order of application. Insert in the
    # EAST first, then the WEST, so both starts use base-chart indices.
    xx=[fold(x,[(198,b),(8,a)]) for x in range(k-1)]
    yy=[fold(y,[(8,a+b)]) for y in range(k-1)]
    assert all(g(x,y)==f(X,Y) for y,Y in enumerate(yy) for x,X in enumerate(xx))

def length_control():
    # Two teeth separated by a gap, with a 3-state internal cycle.
    # On the first tile row A,B,0,A is a physical path of masks,
    # whose teeth are spatially separated; no A->A is permitted.
    k=39;g=8;A,B=2,128;tabs=[];idx={};grid=[]
    for y in range(k-1):
        for x in range(k-1):
            def mark(i):return A if y==0 and g<=i<=g+1 else 0
            ts=((mark(x),0,mark(x+1),0),)
            if x==g and y==0:ts=((A,0,B,0),(B,0,0,0),(0,0,A,0))
            if ts not in idx:idx[ts]=len(tabs);tabs.append(ts)
            grid.append(idx[ts])
    data=encode(k,tabs,grid)
    for period,expected in ((3,'EMPTY'),(14,'OPEN')):
        ans=native(data,(g,),(g,),extra=(f'--period={period}',))
        assert ans.startswith(expected)
    assert not check(1,k,'changing-mask control',data=data,gx=(g,),gy=(g,))
    print('changing-mask control accepts 1+14 extra-step class and rejects 1+3s')

def one_gap(axis,lo,hi,gx):
    k=81;gy=(8,);interval=lo,hi
    data=instance(axis,k,interval)
    ans=native(data,gx,gy)
    assert ans.startswith('EMPTY') and check(axis,k,interval,data=data,gx=gx,gy=gy)
    for q in {lo,hi}:
        def tags(k,i):
            return typ(i,k-1),tuple(min(x,k-1-x)>=4 for x in (i,i+1))
        clip=lambda d:max(-4,min(5,d))
        for split in (0,5,14):
            gaps=[(g,(14 if len(gx)==1 else split if g==8 else 14-split)) for g in reversed(gx)]
            qq=q+sum(n for g,n in gaps if g<q)
            for x in range(k+14-1):
                X=fold(x,gaps);Y=fold(x,[(8,14)])
                assert tags(k+14,x)==tags(k,X)==tags(k,Y)
                assert clip(qq-x)==clip(q-X)

def audit():
    run(['rustc','--edition=2021','-O','src/bin/coupled_mask_grid.rs','-o','target/coupled_mask_grid'],check=True)
    length_control()
    for q in (102,103,104):
        data=bridge(207,q,drat='--drat' in sys.argv)
        gx=(8,198);gy=(8,)
        ans=native(data,gx,gy,q=q)
        assert ans==f'EMPTY h=3 pass=0 horizontal=false start={q-1}'
        assert check(1,207,('two gap',q),data=data,q=q,gx=gx,gy=gy)
        # Real overlapping physical boxes, including ones entirely inside
        # an insertion and at the intersection of the two inserted bands.
        for a,b in ((0,14),(14,0),(5,9),(0,0)):bridge_tags(q,a,b)
    print('two-gap closure: ALL left and right insertion counts; actual box-tag checks passed')
    if '--drat' in sys.argv:print('fresh local drat-trim covers',len(VERIFIED))
    for q in range(2,57,2):one_gap(1,q,q,(72,))
    for q in range(2,24,2):one_gap(2,q,q,(72,))
    one_gap(2,24,24,(8,72))
    one_gap(2,25,79,(8,))
    print('one-gap axis 2 remaining isolate indices: odd q from 1 through 23')
    for a in (1,2):
        op=native(instance(a,207,1),(180,),(8,),extra=('--block=14','--period=14','--rounds=8'))
        assert op=='OPEN (joint strip fixed point)'
        assert not check(a,207,(1,1),gx=(180,),gy=(8,),block=14,rounds=8)
        print('axis',a,'q=1:',op)
if __name__=='__main__':audit()
