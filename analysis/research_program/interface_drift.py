"""Reachable translated frontiers for one 7-to-448 transition in deep rows."""
from collections import Counter,defaultdict,deque
import gzip,json,sys
from pathlib import Path
from .neighbor_diagonal import push
from .tile_family_lp import typ

K=32
S=14
N=3*(K+1)
def full(p,s):
    w=[7]*s+list(p)+[448]*(K+1-s-len(p));w[0]=6;w[-1]=192
    return w
def marks(w,l):
    return [bool(m>>(3*l+b)&1) for m in w for b in range(3)]

def run(axis,width,cap):
    B={(u,v):ws for u,v,ws in json.loads(gzip.decompress(
        Path('target/tile_family_3_5_h6.json.gz').read_bytes()))}
    by=[]
    for j in range(K):
        tab=defaultdict(set)
        for a,b,c,d in B[6,typ(j,K)]:
            if any(min(x,K-x)>=4 and m&16 and m&(40 if axis==1 else 130)
                   for x,m in ((j,a),(j+1,b),(j,c),(j+1,d))):continue
            tab[a,c,d].add(b)
        by.append(tab)
    base=(16,16),tuple(N if j<3*S+2 else j for j in range(N+1))
    states={base:0};queue=deque([base]);edges=[]
    while queue:
        state=queue.popleft();p,pp=state
        old=full(p,S);front=marks(old,0),pp
        for drift in range(-3,4):
            s=S+drift;w=full((),s)
            def walk(j,cost):
                if j==K+1:
                    end=K
                    while end>s and w[end-1]==448:end-=1
                    pat=tuple(w[s:end])
                    f=front
                    try:
                        for l in (2,1,0):f=push(f,marks(w,l),(1,N-2))
                    except AssertionError as e:
                        if str(e)!='forced cycle':raise
                        return
                    # Recenter by extending/contracting only the homogeneous
                    # rooted west prefix and singleton east suffix.
                    part=f[1];assert all(v==N for v in part[:18])
                    assert all(part[j]==j and part.count(j)==1 for j in range(N-18,N))
                    ids={N:N};new=[]
                    for x in range(N):
                        y=x+3*drift
                        v=N if y<0 else part[y] if y<N else N+1+y
                        new.append(ids.setdefault(v,x))
                    node=pat,tuple(new+[N])
                    if node not in states:states[node]=len(states);queue.append(node)
                    edges.append((states[state],states[node],drift,cost))
                    return
                choices=by[j-1].get((w[j-1],old[j-1],old[j]),())
                for m in choices:
                    if j==K and m!=192:continue
                    if j<s and m!=7:continue
                    if s+width<=j<K and m!=448:continue
                    if j==s and m==7:continue
                    v=cost+3-m.bit_count()
                    if v<=cap:w[j]=m;walk(j+1,v)
            walk(1,1)
    print('axis, width, row cap',axis,width,cap,'states',len(states),'edges',len(edges),
          'shift/cost histogram',sorted(Counter(e[2:] for e in edges).items()))
    live=set(states.values())
    while True:
        rem={i for i,j,_,_ in edges if j in live}
        if rem==live:break
        live=rem
    if (width,cap)==(8,15):
        seq=[(16,16),(3,8,264),(33,32,384)]
        ids={p:i for (p,_),i in states.items() if i in live}
        assert len(live)==len(ids)==3
        assert {(i,j,v,c) for i,j,v,c in edges if i in live and j in live}=={
            (ids[p],ids[seq[(h+1)%3]],(-2,-1,-1)[h],6) for h,p in enumerate(seq)}
        print('only recurrent cycle: 3 rows, shift -4, deficit 18')
    return states,edges
if __name__=='__main__':run(*map(int,sys.argv[1:]))
