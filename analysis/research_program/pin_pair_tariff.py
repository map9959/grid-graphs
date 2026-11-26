"""All-depth two-cap coupons on consecutive pitch triples; open lateral cuts."""
from heapq import heappush,heappop
def prices(k,limit,core=None):
    w=3*k;mask=(1<<w)-1
    if core is None:core=mask
    inner=(mask>>1)&~1&core
    pitch=sum(2<<(3*j) for j in range(k))
    start=(pitch,0,tuple(range(k))+tuple(i//3 for i in range(w)))
    best={};q=[];out={}
    def push(z,c):
        if c<=limit and c<best.get(z,limit+1):
            best[z]=c;heappush(q,(c,z))
    def step(st,v,first):
        old,waiting,part=st
        p=[*part,*range(k+w,k+2*w)]
        def rt(i):
            while i!=p[i]:i=p[i]
            return i
        def join(i,j):
            i,j=rt(i),rt(j);p[i]=j;return i!=j
        for i in range(w):
            j=k+w+i
            if (v|old)>>i&1 and not join(k+i,j):return
            if i and v>>(i-1)&3 and not join(j-1,j):return
        roots=[rt(i) for i in range(k)]+[rt(k+w+i) for i in range(w)]
        bill=(waiting&~v).bit_count()
        if not first:bill+=(v&~old&~(v<<1)&~1&core).bit_count()
        return (v,inner&~(old|v|v<<1|v>>1),tuple(roots.index(a) for a in roots)),bill
    def extend(st,c,first):
        a=pitch if first else mask&~(st[0]<<1|st[0]>>1);v=a
        while True:
            z=step(st,v,first)
            if z:push(z[0],c+z[1])
            if not v:break
            v=(v-1)&a
    extend(start,0,True)
    while q:
        c,st=heappop(q)
        if best[st]!=c:continue
        v,waiting,part=st;cost=c+((mask^v)&core).bit_count()+waiting.bit_count()
        labels=part[:k]
        if cost<=limit:out[labels]=min(out.get(labels,limit+1),cost)
        extend(st,c,False)
    return out

def compatible(a,b,pins):
    p=list(range(2*len(a)))
    def rt(i):
        while i!=p[i]:i=p[i]
        return i
    for i in pins:
        j,k=rt(a[i]),rt(len(a)+b[i])
        if j==k:return False
        p[j]=k
    return True

if __name__=='__main__':
    import sys
    k,limit=map(int,sys.argv[1:]);P=prices(k,limit)
    for mask in range(1<<k):
        pins=[i for i in range(k) if mask>>i&1]
        v=min([limit+1]+[x+y for a,x in P.items() for b,y in P.items() if compatible(a,b,pins)])
        print(k,'pins',mask,'joint debit >=',v)
