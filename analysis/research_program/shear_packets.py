"""Factor the two-neighbor inequality through one-sided physical attachment profiles."""
from functools import lru_cache
from collections import Counter
from .crop_frame_rate import canonical


def profiles(lo,hi,separate=False,visit=None,ground=False):
    h=hi-lo+1
    ids={}
    def fixed(r,c):
        return c%3==1 and r-3*(c//3)<lo or c%3==0 and r-3*(c//3)>hi
    def node(r,c):
        for b in range(-1,2):
            if abs(c-3*b-1)+max(0,r-3*b-lo+1)<=1:return ('a',b)
            if abs(c-3*b)+max(0,3*b+hi+1-r)<=1:return ('b',b)
        return r,c
    def num(v):return ids.setdefault(v,len(ids))
    a=num(('a',0));b=num(('b',0))
    # Order by rows so a cycle is rejected early in the mask enumeration.
    sites=[(r,c) for r in range(lo,hi+1) for c in range(3)]
    bundles=[]
    for r,c in sites:
        bundles.append([(tuple(sorted(((r,c),(y,x)))),num(node(r,c)),num(node(y,x)))
                        for y,x in ((r+1,c),(r-1,c),(r,c+1),(r,c-1))
                        if 0<=x<3 and not fixed(y,x)])
    left=([a,b] if separate else [a])+[num(node(r,0)) for r in range(lo-3,hi+1)]
    right=([a,b] if separate else [b])+[num(node(r,2)) for r in range(lo,hi+4)]
    par=list(range(len(ids)));seen=set();options={};layers=[{},{}]
    def root(i):
        while par[i]!=i:i=par[i]
        return i
    def recurse(t,n,ml,mr,mask):
        if t==len(sites):
            if ground:
                for flag in range(4):
                    roots=[root(q) for bit,q in enumerate((a,b)) if flag>>bit&1]
                    if len(set(roots))!=len(roots):continue
                    def lab(q):
                        z=root(q)
                        return -1 if z in roots else z
                    L=(ml,canonical([-1]+[lab(v) for v in left[1:]]))
                    R=(mr,canonical([-1]+[lab(v) for v in right[1:]]))
                    i=layers[0].setdefault(L,len(layers[0]));j=layers[1].setdefault(R,len(layers[1]))
                    gain=n-h+flag.bit_count()-2
                    options[i,j]=max(options.get((i,j),-100),gain)
                    if visit is not None:visit(i,j,gain,(mask,flag))
                return
            if separate and root(a)==root(b):return
            L=(ml,canonical(root(v) for v in left))
            R=(mr,canonical(root(v) for v in right))
            i=layers[0].setdefault(L,len(layers[0]));j=layers[1].setdefault(R,len(layers[1]))
            options[i,j]=max(options.get((i,j),-100),n-h)
            if visit is not None:visit(i,j,n-h,mask)
            return
        recurse(t+1,n,ml,mr,mask)
        added=[]
        for key,u,v in bundles[t]:
            if key in seen:continue
            x,y=root(u),root(v)
            if x==y:break
            added.append((x,key));par[x]=y;seen.add(key)
        else:
            r,c=sites[t]
            recurse(t+1,n+1,ml|((1<<(r-lo+3)) if c==0 else 0),
                    mr|((1<<(r-lo)) if c==2 else 0),mask|1<<t)
        for x,key in reversed(added):par[x]=x;seen.remove(key)
    recurse(0,0,0,0,0)
    return options,list(layers[0]),list(layers[1])


def joint(left,right,separate=False):
    lm,L=left;rm,R=right
    n=len(L);p=list(range(2*n))
    def root(x):
        while p[x]!=x:x=p[x]
        return x
    mask=lm|rm
    while mask:
        bit=mask&-mask;i=bit.bit_length()+int(separate)
        a,b=root(L[i]),root(n+R[i])
        if a==b:return -1
        p[a]=b;mask^=bit
    if separate:
        return 0 if len({root(L[0]),root(L[1]),root(n+R[0]),root(n+R[1])})==4 else -1
    return int(root(L[0])!=root(n+R[0]))


def run(lo,hi,separate=False,unit=False,critical=False,extract=False,ground=False):
    opts,L,R=profiles(lo,hi,separate,ground=ground)
    print("height",hi-lo+1,"block options",len(opts),"left and right profiles",len(L),len(R),flush=True)
    J=[[(j,0 if ground else s) for j,l in enumerate(L) if (s:=joint(l,r,separate))>=(1 if ground else 0)] for r in R]
    d=[0]*len(L);hist={}
    for i in range(100):
        v=max(d);key=tuple(x-v for x in d)
        if key in hist:
            j,w=hist[key]
            scale=1 if unit else 2
            print("cyclic core delta - paid roots bound:" if ground else
                  f"cyclic {scale} * core delta + cuts bound:",v-w,"per",i-j,"blocks",flush=True)
            # Build a rational subaction from a whole orbit of normalized
            # Bellman iterates; check the inequalities on every edge.
            den=i-j;num=v-w
            phi=[max(den*(z[k]+m)-num*t for z,(t,m) in hist.items() if t>=j)
                 for k in range(len(L))]
            rr=[-10**9]*len(R)
            for (l,r),delta in opts.items():rr[r]=max(rr[r],phi[l]+den*scale*delta)
            assert all(rr[r]+den*cut<=phi[l]+num for r in range(len(R)) for l,cut in J[r])
            print("potential verified:",sum(map(len,J)),"compatible joins",flush=True)
            if critical:
                # Directed bipartite equality graph (tag R by adding len(L)).
                from collections import defaultdict
                import sys
                sys.setrecursionlimit(20000)
                g=defaultdict(list); rev=defaultdict(list)
                def edge(a,b):
                    g[a].append(b);rev[b].append(a)
                for (l,r),delta in opts.items():
                    if phi[l]+den*scale*delta==rr[r]:edge(l,len(L)+r)
                for r in range(len(R)):
                    for l,s in J[r]:
                        if rr[r]+den*s==phi[l]+num:edge(len(L)+r,l)
                seen=set();order=[]
                def dfs(x,graph,stack):
                    if x in seen:return
                    seen.add(x)
                    for y in graph[x]:dfs(y,graph,stack)
                    stack.append(x)
                for x in list(g):dfs(x,g,order)
                seen=set();cyc=[];extracted=[]
                for x in reversed(order):
                    comp=[];dfs(x,rev,comp)
                    if len(comp)>1:
                        q=set(comp);cyc.append((len(q),sum(y in q for x in q for y in g[x])))
                        if extract:
                            assert len(q)==428
                            inside={(l,r):dv for (l,r),dv in opts.items()
                                    if l in q and len(L)+r in q and len(L)+r in g[l]}
                            joins={r:[(l,s) for l,s in J[r] if l in q and l in g[len(L)+r]]
                                   for r in range(len(R)) if len(L)+r in q}
                            extracted.append((inside,joins))
                print("equality SCCs (vertices,edges)",Counter(cyc))
                if extract:
                    assert len(extracted)==1
                    return extracted[0]
            return num,den
        hist[key]=i,v
        w=[-10**9]*len(R)
        for (l,r),delta in opts.items():w[r]=max(w[r],d[l]+(1 if unit else 2)*delta)
        d=[-10**9]*len(L)
        for r,v in enumerate(w):
            for l,cut in J[r]:d[l]=max(d[l],v+cut)
    raise ValueError("no recurrence")


if __name__=="__main__":
    import sys
    run(int(sys.argv[1]),int(sys.argv[2]),'--separate' in sys.argv,'--unit' in sys.argv,'--critical' in sys.argv,ground='--ground' in sys.argv)
