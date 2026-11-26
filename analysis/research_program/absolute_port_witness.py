"""Recover a path of column witnesses, not an overlapping physical board."""
from .absolute_ports import column,run,symbols,events

def witness(axis,k,D,isolate=None):
    hist=[]
    bits=run(axis,k,4,D,isolate=isolate,history=hist)
    if not(bits>>D&1):return
    east=(0,)*k;part=();target=D;after=None;path=[]
    for i in reversed(range(k)):
        src,roots=hist.pop();r=i if i<7 else 38-(k-1-i) if k-1-i<7 else 7
        for d,u in roots.items():
            if isolate is not None and d!=min(5,max(-4,isolate-i)):continue
            if r>=32 and d>37-r:continue
            if after is not None and after not in ((4,5) if d==5 else (max(-4,d-1),)):continue
            z=column(src,u,None,axis,r,d,k,4,D,query=(east,part,target))
            if not z:continue
            rows,part,rem=z
            path.append((d,target-rem,rows))
            east=tuple(symbols(r,w,j in (0,k-1))[0] for j,w in enumerate(rows))
            target=rem;after=d;break
        else:raise AssertionError('missing predecessor')
    assert not any(east) and part==() and target==0
    return path[::-1]

def profile(path):
    def cut(w,side):
        out=[]
        for j,y in enumerate(w):
            s=events(y)[side]
            for b in range(3):
                if code:=s>>(2*b)&3:out.append((3*j+b,code))
        return out
    previous=[];total=0;peak=0
    for i,(d,c,w) in enumerate(path):
        L,R=cut(w,0),cut(w,1)
        assert previous==L and len(R)<=4 and c==sum(3-y[1].bit_count() for y in w)
        peak=max(peak,len(R));previous=R;total+=c
        print(i,d,c,w[0][1],w[-1][1],R)
    assert not previous
    print('deficit',total,'peak',peak)
if __name__=='__main__':
    import sys
    p=witness(*map(int,sys.argv[1:]))
    if p:profile(p)
