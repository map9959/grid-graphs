"""Northward graph at a terminating west arm; exact common-root frontier."""
from collections import defaultdict,deque
from functools import lru_cache
import gzip,json,sys
from heapq import heappop,heappush
from pathlib import Path
from .interface_drift import marks
from .neighbor_diagonal import push
from .tile_family_lp import typ

def test(axis,W,closed,S=12):
    # Open graph keeps W tile columns. In the closed graph append the
    # mandatory straight east arm (448, ..., 448, 192).
    k=W+10 if closed else W;N=3*k
    B={(u,v):ws for u,v,ws in json.loads(gzip.decompress(
        Path('target/tile_family_3_5_h6.json.gz').read_bytes()))}
    tabs=[]
    for j in range(k-1):
        t=defaultdict(lambda:defaultdict(list))
        for a,b,c,d in B[6,typ(j,k-1) if closed else min(j,6)]:
            if any((min(x,k-1-x) if closed else x)>=4 and m&16 and m&(40 if axis==1 else 130)
                   for x,m in ((j,a),(j+1,b),(j,c),(j+1,d))):continue
            if closed and any(x>=W and m!=(192 if x==k-1 else 448)
                              for x,m in ((j,a),(j+1,b),(j,c),(j+1,d))):continue
            t[c,d][a].append(b)
        tabs.append(t)
    # Actual incoming first diagonal row with homogeneous bulk on each
    # side of the transition, restricted to the west window if open.
    seed=([6]+[7]*(S-1)+[16,16]+[448]*k)[:k]
    if closed:
        assert W==S+2
        for v in range(13):
            assert all(a==448 for a,b,c,d in B[6,v] if c==448)
        assert all(b==192 for a,b,c,d in B[6,12] if d==192)
        assert W>=S+2;seed[-1]=192
    root=tuple(N if j<3*S+2 else j for j in range(N))+ (N,)
    # Seed partition uses connections in the processed band. In the
    # open projection these known connections can also be retained.
    initial=tuple(seed),root;states={initial:0};q=deque([initial]);edges=[]
    @lru_cache(None)
    def rows(old):
        ans=[]
        def grow(w):
            j=len(w)-1
            if j==k-1:ans.append(tuple(w));return
            for b in tabs[j][old[j:j+2]].get(w[-1],()):grow([*w,b])
        for a in tabs[0][old[:2]]:grow([a])
        return ans
    while q:
        v=q.popleft();old,part=v
        for y in rows(old):
            f=marks(old,0),part
            try:
                for l in (2,1,0):f=push(f,marks(y,l),(1,N-2) if closed else (1,))
            except AssertionError as e:
                if str(e)!='forced cycle':raise
                continue
            nxt=y,tuple(f[1])
            if nxt not in states:states[nxt]=len(states);q.append(nxt)
            edges.append((states[v],states[nxt],sum(3-m.bit_count() for m in y)))
    term={i for (w,_),i in states.items() if w[0]!=6}
    live=set(term)
    while True:
        pre={i for i,j,c in edges if i in term and j in live}
        if pre==live:break
        live=pre
    print('axis,width,closed',axis,W,closed,'states/edges',len(states),len(edges),
          'terminated/live',len(term),len(live))
    if closed:
        remaining=set(states.values());steps=0
        while remaining:
            pre={i for i,j,c in edges if j in remaining}
            if pre==remaining:break
            remaining=pre;steps+=1
        assert not remaining
        print('longest continuation in bulk tile rows',steps-1)
        if S in (13,15):assert steps=={13:10,15:13}[S]
    elif W==4:
        # Least prefix cost to a zero-loss terminated self-loop.
        goals={i for i,j,c in edges if i==j and i in live and c==0}
        graph=defaultdict(list)
        for i,j,c in edges:graph[i].append((j,c))
        heap=[(0,0,0)];done=set()
        while heap:
            c,h,i=heappop(heap)
            if i in done:continue
            done.add(i)
            if i in goals:break
            for j,v in graph[i]:heappush(heap,(c+v,h+1,j))
        assert i in goals and (c,h)==(4,2)
        print('open fringe reaches zero-loss loop in',h,'rows, deficit',c)
    return states,edges,live
if __name__=='__main__':test(int(sys.argv[1]),int(sys.argv[2]),'--closed' in sys.argv,
                             int(sys.argv[3]) if sys.argv[3:4] and sys.argv[3]!='--closed' else 12)
