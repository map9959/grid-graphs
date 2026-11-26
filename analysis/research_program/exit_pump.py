"""Pump a full-length boundary strip with both gaps opening onto that side."""
from functools import lru_cache
from .odd_frames import frame,DIR,rotate
from .defect_window import table
from .sector_oriented import assign
from .seven_threshold import masks

@lru_cache(None)
def tables(n):return table(n)

memo={}
def run(H,n=119,code='0211',root=0,quiet=False):
    assert n>=119 and (n-35)%42==0
    typ,patch,star=tables(n);word=tuple(map(int,code))
    assert len(word)==4 and sum(t in (0,2) for t in word)==2
    marks=frame(n,word);corner=((0,0),(0,n-1),(n-1,n-1),(n-1,0))[root]
    parent={corner:-1};queue=[corner]
    for i,j in queue:
        for d,(a,b) in enumerate(DIR):
            u=i+a,j+b
            if u in marks and min(*u,n-1-u[0],n-1-u[1])==0 and u not in parent and (marks[u] or marks[i,j]):
                queue.append(u);parent[u]=(d+2)%4
    # Use the exterior terminal only if the entire omitted perimeter
    # arc between the two bottom endpoints is forced.
    outside=[(r,0) for r in range(H-1,n)]+[(n-1,j) for j in range(1,n)]+[(r,n-1) for r in reversed(range(H-1,n-1))]
    grounded=all(marks[a] or marks[b] for a,b in zip(outside,outside[1:]))
    sig=(n,H,grounded,tuple(sorted((u,v) for u,v in marks.items() if u[0]<H)),
         tuple(sorted((u,v) for u,v in parent.items() if u[0]<H)))
    if quiet and sig in memo:return memo[sig]
    start=tuple(range(H+1));marg=12
    assert H<20
    def rep(j):return j if j<marg else j if j>=n-marg else marg+(j-marg)%3
    @lru_cache(None)
    def options(j):
        return [m for m in range(1<<H) if all((i,j) not in marks or m>>i&1==marks[i,j] for i in range(H))]
    @lru_cache(None)
    def step(b,p,c,tie):
        # Retain an external terminal incident at the two lower corners
        # of the strip. The portion of the unbroken perimeter below this
        # strip joins them disjointly from its interior.
        T=H;off=H+1;ds=list(p)+list(range(off,off+H))
        def root(u):
            while ds[u]!=u:u=ds[u]
            return u
        def edge(a,b):
            a,b=root(a),root(b);ds[a]=b;return a!=b
        for i in range(H):
            if (b|c)>>i&1 and not edge(i,off+i):return
            if i+1<H and c>>i&3 and not edge(off+i,off+i+1):return
        if tie and not edge(T,off+H-1):return
        z=[root(off+i) for i in range(H)]+[root(T)]
        return tuple(z.index(u) for u in z)
    def extensions(j,a,b):
        first=j==0;last=j==n-1
        for c in ([0] if last else options(j+1)):
            if c&((b<<1)|(b>>1)):continue
            if not(first or last) and any(patch(typ(1,r,j-1))[m] for r,m in enumerate(masks(a,b,c,H))):continue
            yield c
    @lru_cache(None)
    def legal(j,a,b):return tuple(extensions(j,a,b))
    @lru_cache(None)
    def transitions(j,a,b,p,west):
        out=[];first=j==0;last=j==n-1
        for c in legal(j,a,b):
            dest=step(b,p,c,grounded and j==n-2) if not last else start
            if dest is None:continue
            for nw,ds in assign(b,west,0 if last else b|c,H):
                pay=0
                for r,d in enumerate(ds[:-1]):
                    if (r,j) in parent and parent[r,j]!=d:break
                    ports=tuple(i for i,(dx,dy) in enumerate(DIR) if 0<=r+dx<n and 0<=j+dy<n)
                    nb=(c>>r&1,b>>(r+1)&1,a>>r&1,(b>>(r-1)&1) if r else 0)
                    m=(b>>r&1)+sum(nb[i]<<(i0+1) for i0,i in enumerate(ports))
                    q=star(typ(0,r,j),ports,d,(r,j)==corner,len(ports)==2)[m]
                    # Preserve the side of the charged exit, including
                    # exits on the *short*, perpendicular strip ends.
                    if (r,j) not in parent and q==72 and len(ports)==3:
                        inward=1 if r==0 else 0 if first else 2
                        if d!=inward or pay:break
                        pay=1+j%3 if r==0 else 4+r if first else 4+H+r
                    elif q:break
                else:out.append((b,c,dest,nw,pay))
        return out
    dp={(0,b,step(0,start,b,grounded),0,0) for b in options(0)}
    # Snapshot BEFORE each column. Include exit phase and all frontier data.
    snapshots={};peak=0;repeat=None
    for j in range(n):
        # At the entry and exit of the periodic interval the adjacent
        # mask tests must also be stationary; choose snapshots far inside.
        if marg<=j<n-marg and j%3==0 and repeat is None:
            if snapshots.pop(j-42,None)==dp:repeat=(j-42,j,len(dp))
            snapshots[j]=dp
        nd=set()
        for a,b,p,west,used in dp:
            for v,c,d,nw,pay in transitions(rep(j),a,b,p,west):
                if not(used and pay):nd.add((v,c,d,nw,pay or used))
        dp=nd;peak=max(peak,len(dp))
    charges={u for *_,u in dp}
    if not quiet:print(f'n={n}, H={H}, frame={code}, root={root}, repeat={repeat}, peak={peak}; '
          f'zero={0 in charges}, top phases={sorted(u-1 for u in charges if 1<=u<=3)}, '
          f'short-end codes={sorted(u for u in charges if u>3)}',flush=True)
    memo[sig]=(repeat,charges)
    return repeat,charges

def screen(H,n):
    from itertools import product
    from .square_dual_physical import trans
    total=excluded=0
    for word in product(range(4),repeat=4):
        if sum(x in (0,2) for x in word)!=2 or min(rotate(word,g) for g in range(8))!=word:continue
        total+=1;sizes=[];joint={};marks=frame(n,word)
        for root in range(4):
            candidates={(i,j) for i in range(n) for j in range(n) if min(i,j,n-1-i,n-1-j)==0}
            for side in range(4):
                g=(-side)%4;w=rotate(word,g)
                repeat,ok=run(H,n,''.join(map(str,w)),(root+g)%4,True)
                assert repeat is not None,(w,root,g)
                def accept(site):
                    i,j=trans(*site,n,g)
                    u=1+j%3 if i==0 else 4+i+(H if j else 0) if i<H-1 else 0
                    return u in ok
                candidates={s for s in candidates if accept(s)}
            sizes.append(len(candidates))
            # Rerooting inside a fixed perimeter component does not
            # change where the path leaves the opposite component.
            q=[trans(0,0,n,root)];seen=set(q)
            for i,j in q:
                for a,b in DIR:
                    u=i+a,j+b
                    if u in marks and min(*u,n-1-u[0],n-1-u[1])==0 and u not in seen and (marks[i,j] or marks[u]):
                        seen.add(u);q.append(u)
            key=min(seen);candidates-=seen
            if key in joint:joint[key]&=candidates
            else:joint[key]=candidates
        merged=[len(v) for v in joint.values()]
        excluded+=int(0 in merged)
        print(''.join(map(str,word)),'exit locations by root',sizes,'shared by component',merged,flush=True)
    print('uniform exclusions',excluded,'of',total,'frames',flush=True)
if __name__=='__main__':
    import sys
    a=sys.argv[1:]
    if a[0]=='--screen':screen(*map(int,a[1:]))
    else:run(int(a[0]),int(a[1]) if len(a)>1 else 119,a[2] if len(a)>2 else '0211',int(a[3]) if len(a)>3 else 0)
