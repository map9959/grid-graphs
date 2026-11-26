"""Finite frontier upper certificate for arbitrary three-layer frames around Q_k."""
from functools import lru_cache


def canonical(labels):
    m={}
    return tuple(m.setdefault(x,len(m)) for x in labels)


@lru_cache(None)
def step(side,phase,state,mask):
    oldmask,part=state
    lanes=3 if side else 6
    # slots after old lane vertices: static rod root on the side, or
    # top current root, bottom current/next roots on the paired strips.
    nroot=1 if side else 3
    size=lanes+nroot
    parent=list(range(size+lanes+2))
    def root(x):
        while parent[x]!=x:
            parent[x]=parent[parent[x]]
            x=parent[x]
        return x
    representatives={}
    for i,v in enumerate(part):
        parent[i]=representatives.setdefault(v,i)
    def link(x,y):
        a,b=root(x),root(y)
        if a==b:return False
        parent[a]=b
        return True
    for i in range(lanes):
        if ((oldmask|mask)>>i)&1 and not link(i,size+i):return
        if i%3 and ((mask>>(i-1))&3) and not link(size+i-1,size+i):return
    # Each newly introduced lane 0 (or 3) contacts one physical crop
    # vertex. Force this edge when EITHER endpoint is selected.
    if side:
        if not link(size,lanes):return
        roots=[lanes]
    else:
        if (phase==1 or mask&1) and not link(size,lanes):return
        if (phase==0 or mask&8) and not link(size+3,lanes+1+(phase==2)):return
        roots=[lanes,lanes+1,lanes+2]
        if phase==2:roots=roots[1:]+[size+lanes]
    slots=list(range(size,size+lanes))+roots
    return mask,canonical(root(x) for x in slots)


def iterate(side,length,transition=step):
    lanes=3 if side else 6
    d={(0,tuple(range(lanes+(1 if side else 3)))):0}
    snapshots=[]
    for i in range(length):
        nd={}
        for s,v in d.items():
            for m in range(1<<lanes):
                t=transition(side,i%3,s,m)
                if t is not None:nd[t]=max(nd.get(t,-1),v+m.bit_count())
        d=nd
        if i%3==2:snapshots.append(d)
    return snapshots


def graph_step(side,phase,state,mask):
    """Independent transition: multigraph DFS and E=V-components, not union-find."""
    old,labels=state
    width=3 if side else 6
    ports=list(labels[width:])
    current=[100+i for i in range(width)]
    vertices=set(labels)|set(current)|{200}
    edges=[]
    for i,p in enumerate(current):
        if (old|mask)&(1<<i):edges.append((labels[i],p))
        if i%3!=2 and mask&(3<<i):edges.append((p,current[i+1]))
    if side:
        edges.append((ports[0],current[0]))
    else:
        if mask&1 or phase==1:edges.append((ports[0],current[0]))
        if mask&8 or phase==0:edges.append((ports[-1] if phase==2 else ports[1],current[3]))
        if phase==2:ports=ports[1:]+[200]
    adj={p:[] for p in vertices}
    for a,b in edges:
        adj[a].append(b);adj[b].append(a)
    comps={}
    for p in vertices:
        if p in comps:continue
        todo=[p];comps[p]=p
        while todo:
            for x in adj[todo.pop()]:
                if x not in comps:
                    todo.append(x);comps[x]=p
    if len(edges)!=len(vertices)-len(set(comps.values())):return
    return mask,canonical(comps[x] for x in current+ports)


def audit():
    for side,rate in [(True,3),(False,7)]:
        fast=iterate(side,12)
        independent=iterate(side,12,lru_cache(None)(graph_step))
        assert independent==fast
        old,new=fast[-2:]
        assert new=={state:v+rate for state,v in old.items()}
        print("side" if side else "top+bottom","(columns,states,max)",
              [(3*(i+1),len(s),max(s.values())) for i,s in enumerate(fast)],
              "all terminal scores advance by",rate)
    caps=[cap([-1]*3,[0]*3),cap([0,0,0,1,1],[0,1,0,0,1]),
          cap([0,0,1,2,0],[1,0,0,0,0]),cap([0,1],[0,0]),cap([0,0],[1,0])]
    assert caps==[cap([-1]*w,[0]*w) for w in (3,5,5,2,2)]
    print("corner, top tail, bottom tail, left tail, right tail maxima:",caps)
    C=2-7+4*caps[0]+sum(caps[1:])
    print(f"frame upper 13*k+{C}, target 14*k+25; deficit >= k-{C-25}")
    audit_ports()


def audit_ports():
    from .nested_renewal import direct_q
    for n in (8,14):
        k=(n-2)//3
        F=direct_q(n)
        p=list(range(n*n))
        def find(x):
            while x!=p[x]:x=p[x]
            return x
        for x in range(n*n):
            for y in ([x+1] if x%n<n-1 else [])+([x+n] if x+n<n*n else []):
                if x in F or y in F:
                    a,b=find(x),find(y)
                    assert a!=b
                    p[a]=b
        A=[find(3*j+1) for j in range(k+1)]
        for j in range(k-1):
            for i in range(3):
                c=3*j+i
                assert find(c)==A[j]
                assert find((n-1)*n+c)==A[j+1+(i==2)]
                assert (c in F)==(i==1)
                assert ((n-1)*n+c in F)==(i==0)
        for r in range(2,n):assert r*n in F and find(r*n)==A[1]
        for r in range(n-2):assert r*n+n-1 in F and find(r*n+n-1)==A[k]
        print("direct forest and retained boundary ports verified on Q",k)


def cap(roots,forcing):
    # Exhaust the tiny corner rectangles by ordinary component sets.
    n=max(roots,default=-1)+1
    d={(0,tuple(range(3+n))):0}
    for ext,force in zip(roots,forcing):
        nd={}
        for (old,part),v in d.items():
            for m in range(8):
                vertices=set(part)|{100,101,102}
                e=[(part[i],100+i) for i in range(3) if (m|old)&(1<<i)]
                e += [(100+i,101+i) for i in range(2) if m&(3<<i)]
                if ext>=0 and (force or m&1):e.append((100,part[3+ext]))
                comps=[{p} for p in vertices]
                for a,b in e:
                    x=next(s for s in comps if a in s)
                    y=next(s for s in comps if b in s)
                    if x is y:break
                    x.update(y);comps.remove(y)
                else:
                    q=canonical(next(i for i,s in enumerate(comps) if p in s)
                                for p in (100,101,102,*part[3:]))
                    nd[m,q]=max(nd.get((m,q),-1),v+m.bit_count())
        d=nd
    return max(d.values())


if __name__=='__main__':
    audit()
