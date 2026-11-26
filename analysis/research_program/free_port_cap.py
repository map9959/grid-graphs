"""Variable cut words: exact cap class tariff coupled to the free-port seam."""
from collections import Counter,defaultdict
from functools import lru_cache
from .seam_rank_chart import model,Q,sys,solve

def cap(H,N,d,h,side,ns,A,b,obj,price):
    mask=(1<<h)-1
    def ax(x,K):return x if x<d+4 else 2*(d+4)+3+x-K if x>=K-d-4 else d+4+(x-d-4)%3
    def xtype(x):return ax(x,N) if 0<=x<N else -1
    # Each transition adds one cap column plus the first seam-site bit.
    # Only true cap sites enter the cap partition; the extra bit determines
    # whether there is a crossing edge at its nearest cap site.
    init=(0,tuple(range(h)),0)
    @lru_cache(None)
    def advance(st,v):
        old,part,tag=st
        if old&((v<<1)|(v>>1)):return
        p=[*part,*range(h,2*h)]
        def rt(i):
            while p[i]!=i:i=p[i]
            return i
        def join(a,b):
            a,b=rt(a),rt(b);p[a]=b;return a!=b
        for i in range(h):
            if (old|v)>>i&1 and not join(i,h+i):return
            if i and (v>>(i-1))&3 and not join(h+i-1,h+i):return
        active=[rt(h+i) for i in range(h)]
        tagged={rt(i) for i in range(h) if tag>>i&1}
        if v>>(h-1):tagged.add(active[-1])
        new=tuple(active.index(u) for u in active);flags=sum(1<<i for i in range(h) if new[i]==i and active[i] in tagged)
        return (v,new,flags),len(tagged-set(active))
    # The initial dummy sites have no marks and no terminal tags.
    flow=defaultdict(Counter);marg=defaultdict(Counter);seen=set();states={init}
    for j in range(N):
        key=xtype(j-1),xtype(j),xtype(j+1);fresh=set()
        for st in sorted(states):
            for v in range(2<<h):
                z=advance(st,v)
                if z is None:continue
                nx,gain=z;fresh.add(nx);ident=(side,key,st,v)
                if ident in seen:continue
                seen.add(ident);x='v'+str(len(ns));ns['cap',ident]=x
                obj[x]=(v&mask).bit_count()+price*(gain+(nx[2].bit_count() if j==N-1 else 0))
                if j:flow[key[:2],st][x]+=1
                if j<N-1:flow[key[1:],nx][x]-=1
                marg[key[1],v>>h,(v>>(h-1))&1][x]+=1
        states=fresh
    end=0 if side%2==0 else H-1;t=(3,1,2,0)[side]
    for atom,x in ns.items():
        if atom[0]!='s':continue
        _,(y,j),m,nb,o=atom
        if side>=2:y,j=j,y
        if y==ax(end,H):marg[j,m,nb[t]][x]-=1
    for cs in [*flow.values(),*marg.values()]:
        A.append(([(x,v) for x,v in cs.items() if v],'='));b.append(0)

def test(n,h,d):
    H=n-2*h;four='--four-ports' in sys.argv;N=H if four else n;price=Q(next(z[8:] for z in sys.argv if z.startswith('--price=')))
    assert '--free-ports' in sys.argv
    A,b,obj,ns,_=model(H,N,d)
    for side in range(4 if four else 2):cap(H,N,d,h,side,ns,A,b,obj,price)
    score,_,_=solve(A,b,obj,ns,interior=True);k=n//3
    if four:score+=4*h*h
    print('free-port score (incl. last class)',score,'over comb',score-(3*k*k+5*k+(3*k-13)//10),len(ns),len(A))
if __name__=='__main__':test(*map(int,sys.argv[1:4]))
