"""Independent certificate check: search directly for a word escaping each claimed DFA.

No subset construction or minimization here. Prove budget lower bounds
by length induction before using them to prune a composition.
"""
from functools import lru_cache
from heapq import heappop,heappush


def product_checker(local,ALL):
    memo={};keep={};calls=0
    def image_in(left,drop,edge,z,right):
        nonlocal calls
        if not left[1] or right is ALL:return
        key=id(left),drop,edge,id(right)
        keep[id(left)]=left;keep[id(right)]=right
        if memo.get(key,-1)>=z:return
        A,F=left;D,G=right;arcs,ends=local(edge,drop)
        start=(0,0,0);dist={start:0};heap=[(0,start)]
        while heap:
            c,state=heappop(heap)
            if dist[state]!=c:continue
            a,t,d=state
            assert a not in F or d in G or c+ends.get(t,99999)>z,('bad projection',edge,z,state)
            for l,r,v,w in arcs[t]:
                if c+w>z or l not in A[a]:continue
                n=A[a][l],v,D[d].get(r,-1) if d>=0 else -1
                if c+w<dist.get(n,99999):dist[n]=c+w;heappush(heap,(c+w,n))
        calls+=1;memo[key]=z
    return image_in,lambda:calls


def verify(width,targets,splits,bound,lang,local,ALL,EMPTY):
    image_in,count=product_checker(local,ALL)
    def cover(n,g,j,z,target):
        if target is ALL:return
        for drop in (0,1):
            if not 0<=j-drop<n:continue
            m=floor(n-1,g,j-drop)
            for c in range(m,z+1):
                left=language(n-1,g,j-drop,c)
                image_in(left,drop,'L' if n==1 and g else '',z-c,target)
    @lru_cache(None)
    def floor(n,g,j):
        assert 0<=j<=n
        if n==0:return 0
        claim=bound(n,g,j)
        # Partition into disjoint intervals. The target cost is a sum
        # of physical triple costs from the *same* global orientation.
        for k in range(1,n):
            if all(floor(k,g,t)+floor(n-k,0,j-t)>=claim for t in range(max(0,j+k-n),min(k,j)+1)):
                return claim
        if claim>0:cover(n,g,j,claim-1,EMPTY)
        return claim
    @lru_cache(None)
    def language(n,g,j,z):
        if z<floor(n,g,j):return EMPTY
        L=lang(n,g,j,z)
        if n:cover(n,g,j,z,L)
        elif g: # any number of zero slit symbols must be accepted
            a=0;seen=set()
            while a not in seen:
                assert a in L[1];seen.add(a);a=L[0][a][0]
        else:assert L is ALL
        return L
    def disjoint(P,Q):
        # Build the predecessor relation only for synchronously
        # reachable pairs, rejecting any reachable common final.
        p,f=P;q,g=Q
        seen={(0,0)};work=[(0,0)]
        for a,b in work:
            assert a not in f or b not in g
            for x,c in p[a].items():
                u=x%2;v=(x//2)%2;rightward=x//4
                y=2*u+v+4*int(bool(u or v) and not rightward)
                if y in q[b]:
                    t=c,q[b][y]
                    if t not in seen:seen.add(t);work.append(t)
    for j,(target,n) in enumerate(zip(targets,splits)):
        cap=2*width+2*j-4*target
        for r in range(max(0,j-width+n),min(n,j)+1):
            a,b=floor(n,1,r),floor(width-n,1,j-r)
            for z in range(a,cap-b+1):
                disjoint(language(n,1,r,z),language(width-n,1,j-r,cap-z))
    print('independent product inclusion checks',count(),'rank exclusions',len(targets),flush=True)
