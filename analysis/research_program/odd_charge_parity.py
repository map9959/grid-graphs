"""Integer parity test on *unaveraged* star/patch counts at the 1/14 budget."""
from .square_dual_physical import inspect,DIR,SYM,MASKS,trans
from .square_current import states
from collections import Counter,defaultdict
from itertools import product
from functools import lru_cache
import sys

def build(n,period=6,sector=0,depth=None):
    family=inspect(20);N=[n,n-2];types=[];domain=[];mass=Counter()
    if depth is None:depth=int(next((s[2:] for s in sys.argv if s.startswith('d=')),6))
    def ix(i,S,d,p):return i if i<d else 2*d+p+i-S if i>=S-d else d+(i-d)%p
    def typ(t,i,j):
        return (t,ix(i,N[t],depth-t,period),ix(j,N[t],depth-t,period))+(tuple(max(-sector,min(sector,z)) for z in (i-j,i+j+1-N[t])) if sector else ())
    for t,S in enumerate(N):
        dic={};mp={}
        for i,j in product(range(S),repeat=2):
            k=typ(t,i,j);dic[k]=(i,j);mp[i,j]=k;mass[k]+=1
        types.append(dic);domain.append(mp)
    rd={};raw=[];ixs={};qs=[];labels=[]
    def idr(k):return rd.setdefault(k,len(rd))
    for t,S in enumerate(N):
        for key,(i,j) in sorted(types[t].items()):
            ds=[s for s,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n];events=[]
            if t==1:events=MASKS
            else:
                for f,sig in states(ds):
                    nb=tuple(sig[s][int(s<2)] if s in sig else 9 for s in range(4))
                    out=next((s for s,v in sig.items() if v[2]==(1 if s<2 else -1)),-1)
                    if len(ds)==2 and not f:continue
                    if (i,j)==(0,0):
                        if out!=-1:continue
                    elif out==-1 and (f or 1 in nb):continue
                    events.append((f,nb,out))
            dest=[]
            for ev in events:
                imgs=[]
                for g in range(8):
                    pt=tuple(ix(v,S,6-t,3) for v in trans(i,j,S,g))
                    if t:v=SYM[ev][g]
                    else:
                        f,nb,out=ev;rot=lambda d:((2-d if g&4 else d)+g%4)%4
                        ww=[9]*4
                        for d in range(4):ww[rot(d)]=nb[d]
                        v=f,tuple(ww),rot(out) if out>=0 else -1
                    imgs.append((pt,v))
                q=family['p' if t else 's',min(imgs)]*1008;assert q.denominator==1
                if q>72:continue
                col=[idr(('norm',key))]
                if not t and ev[0]:col.append(idr(('score',)))
                dest.append((ev,len(raw)));raw.append(col);qs.append(int(q));labels.append((key,ev))
            ixs[key]=dest
    def link(t0,t1,di,dj,fun):
        # Components of the incidence graph: both sums cover exactly
        # the same physical pairs. Boundary types distinguish outsiders.
        parent={}
        def root(x):
            while x in parent:x=parent[x]
            return x
        used=set()
        for (i,j),u in domain[t0].items():
            v=domain[t1].get((i+di,j+dj))
            if v is None:continue
            a,b=(0,u),(1,v);used.update((a,b));a,b=root(a),root(b)
            if a!=b:parent[max(a,b)]=min(a,b)
        for side,k in sorted(used):
            cell=root((side,k))
            for e,ci in ixs[k]:
                r=idr(('link',t0,t1,di,dj,cell,fun(side,e)))
                raw[ci].append(~r if side else r)
    for d,(a,b) in enumerate(DIR[:2]):
        def star(s,e):
            f,nb,out=e;z=(d+s*2)%4;u=nb[z]
            return (f,u,int(out==z)) if not s else (u,f,(int(out!=z) if f or u else 0))
        link(0,0,a,b,star)
        def patch(s,m):
            return tuple(m>>(3*(i-a*s)+j-b*s)&1 for i in range(a,3) for j in range(b,3))
        link(1,1,a,b,patch)
    for i,j in product(range(3),repeat=2):
        dirs=[s for s,(a,b) in enumerate(DIR) if 0<=i+a<3 and 0<=j+b<3]
        def local(side,e):
            if side:return (e[0],*(e[1][d] for d in dirs))
            return (e>>(3*i+j)&1,*(e>>(3*(i+DIR[d][0])+j+DIR[d][1])&1 for d in dirs))
        link(1,0,i,j,local)
    rhs=[idr(('norm',k)) for k,count in mass.items() if count%2]
    k=(n-2)//3
    if (3*k*k+7*k-(k-5)//7)%2:rhs.append(rd['score',])
    return raw,qs,rhs,len(rd),labels,rd,mass

def possible(cols,qs,rd,mass,labels,profile,only=None):
    from collections import deque
    take=[q==0 or (q in profile and (only is None or labels[i] in only)) for i,q in enumerate(qs)]
    dirs=defaultdict(list)
    links={i for k,i in rd.items() if k[0]=='link'}
    # If a position type occurs just once and it is the unique defect,
    # that occurrence cannot be occupied by any of its zero-charge atoms.
    fixed=set()
    if only and len(only)==1 and len(profile)==1:
        k,e=next(iter(only))
        if mass[k]==1:fixed.add(k)
    for i,cs in enumerate(cols):
        if labels[i][0] in fixed and not qs[i]:take[i]=False
        if take[i]:
            for r in cs:dirs[r].append(i)
    count=Counter({r:len(v) for r,v in dirs.items()});dead=deque()
    for r in links:
        for s in (r,~r):
            if not count[s]:dead.append(~s)
    while dead:
        for i in dirs[dead.popleft()]:
            if take[i]:
                take[i]=False
                for r in cols[i]:
                    count[r]-=1
                    if not count[r] and (r if r>=0 else ~r) in links:dead.append(~r)
    if any(not count[rd['norm',k]] for k in mass):return []
    return take

def test(n):
    cols,qs,rhs,nr,labels,rd,mass=build(n)
    take=possible(cols,qs,rd,mass,labels,(36,72))
    assert take
    if '--dimers' in sys.argv:
        from .charge_dimers import extend
        extend(n,cols,qs,rd,mass,labels,take)
        # Never resurrect initially excluded site events.
        for i,ok in enumerate(take):
            if not ok:qs[i]=73
        take=possible(cols,qs,rd,mass,labels,(36,72));nr=len(rd);assert take
    piv={}
    def bits(cs):
        z=0
        for i in cs:z^=1<<(i if i>=0 else ~i)
        return z
    def insert(z):
        while z:
            i=z.bit_length()-1
            if i not in piv:piv[i]=z;return
            z^=piv[i]
    for cs,q,ok in zip(cols,qs,take):
        if not q and ok:insert(bits(cs))
    # Canonical quotient coordinates, including nonpivots below leading ones.
    def rem(z):
        r=0
        while z:
            i=z.bit_length()-1
            if i in piv:z^=piv[i]
            else:r^=1<<i;z^=1<<i
        return r
    z=rem(bits(rhs));poss=defaultdict(set)
    for cs,q,ok in zip(cols,qs,take):
        if q and ok:poss[q].add(rem(bits(cs)))
    print('side',n,'rows',nr,'zero rank',len(piv),'target quotient weight',z.bit_count(),
          'distinct single-defect syndromes',{q:len(v) for q,v in sorted(poss.items())},flush=True)
    print('profile (72) survives',z in poss[72],'; (36,36) survives',any(z^x in poss[36] for x in poss[36]),flush=True)
    keep=[e for e,q,cs,ok in zip(labels,qs,cols,take) if ok and q==72 and rem(bits(cs))==z]
    print('72 survivors by type',dict(Counter(k[0] for k,e in keep)),flush=True)
    assert not any(z^x in poss[36] for x in poss[36])
    return keep
if __name__=='__main__':
    if '--uniform' in sys.argv:
        for n in (35,77):test(n)
    else:test(int(sys.argv[1]))
