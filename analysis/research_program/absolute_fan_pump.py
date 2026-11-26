"""Blank tile cycles which preserve the absolute matched-row fan as k grows."""
from .absolute_port_fan import solve,candidate,check
from .absolute_ports import BASE,CORE,step,piece,tab,events
from .ordered_ports import glue

def inspect(rows,r,d,axis,prev):
    z=BASE;f,l,h,done=CORE,0,0,();hist={};cost=0;cycles=[];events_at=[]
    k=len(rows)
    for j,w in enumerate(rows):
        end=j in (0,k-1)
        if j:
            jj=j-1 if j-1<7 else 38-(k-j) if k-j<7 else 7
            assert w in tab(axis,r,jj,d)[rows[j-1]]
        a,b,_=events(w)
        if a or b:events_at.append(j)
        z=step(z,w,end,r);assert z is not None
        f,l,h,done=piece(w,f,l,h,done,end,r,4,False)
        cost+=3-w[1].bit_count()
        state=(w,z,f,l,h,done,cost)
        if 7<=j<k-7:
            if state in hist and j-hist[state] in (1,2):cycles.append((hist[state],j))
            hist[state]=j
    trees=done+tuple(x for x in f[2] if x&1 and x!=3)
    nxt=glue(l,h,trees,prev,4);assert nxt is not None
    assert 2 not in z[2]
    return (not events_at,next(((a,b) for a,b in cycles if b<min(events_at,default=k)),None),
            next(((a,b) for a,b in cycles if a>max(events_at,default=-1)),None),nxt)

def cover(t,verbose=True,pump=0):
    k=39+14*t;q=19+4*t;s=13+2*t
    path=solve(1,k,q,s,False);assert path
    prev=();bad=[];_,costs=candidate(k,q,s);anchors=[]
    for i,w in enumerate(path):
        r=i if i<7 else 38-(k-1-i) if k-1-i<7 else 7
        empty,north,south,nxt=inspect(w,r,min(5,max(-4,q-i)),1,prev)
        anchors.append((empty,north,south))
        # Extra full costs on these rows must be zero; checked by the
        # cycle-state equality above, not inferred from portlessness.
        if empty:ok=north
        elif i<=q+11:ok=north and south
        else:ok=north
        if not ok:bad.append(i)
        if i==7:assert prev==nxt==() and costs[i]==3
        if q+9<=i<=q+11:assert prev==nxt==(1,0) and costs[i]==6
        prev=nxt
    assert prev==()
    if verbose:print('t',t,'missing blank-cycle anchors at',bad,flush=True)
    if pump:
        assert not bad and pump>0
        kk=k+42*pump;qq=q+12*pump;ss=s+6*pump;out=[];prev=()
        for i in range(kk):
            if i<8:j=i;shift=2*pump
            elif i<8+12*pump:j=7;shift=2*pump
            elif i<qq+9:j=i-12*pump;shift=2*pump
            elif i<qq+9+30*pump:
                div,mod=divmod(i-qq-9,3);j=q+9+mod;shift=2*pump+4*div
            else:j=i-42*pump;shift=42*pump
            empty,north,south=anchors[j]
            if empty:shift=42*pump
            w=path[j]
            for cycle,n in ((south,42*pump-shift),(north,shift)):
                if not n:continue
                a,b=cycle;assert n%(b-a)==0
                w=w[:b+1]+w[a+1:b+1]*(n//(b-a))+w[b+1:]
            assert len(w)==kk
            r=i if i<7 else 38-(kk-1-i) if kk-1-i<7 else 7
            *_,prev=inspect(w,r,min(5,max(-4,qq-i)),1,prev)
            out.append(w)
        assert prev==()
        check(out,1,qq,ss)
    return not bad
if __name__=='__main__':
    import sys
    if sys.argv[1:]:
        for t in map(int,sys.argv[1:]):cover(t)
    else:
        for t in range(9):
            assert solve(1,39+14*t,19+4*t,13+2*t,False)
        for t in range(9,12):assert cover(t,pump=1)
