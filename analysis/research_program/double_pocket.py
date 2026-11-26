"""Contract two-column diagonal rewrites, including shared intervening U ports."""
from functools import lru_cache
from itertools import product
from .crop_frame_rate import canonical


def packets(lo=-1,hi=4):
    # Relative row origin 3j; columns 0 and 3 are the immutable separators.
    # Bottom rod starts at row 2 on column 0, row 5 on column 3.
    # Top rods end at lo-1 on column 1 and lo+2 on column 4.
    assert -4<=lo<=1 and hi>=max(2,lo)
    splits=list(range(lo,1)) # unoccupied, non-root ports between top and bottom
    stride=2+len(splits)
    def label(r,c):
        for start in (0,3):
            # Are we within the star support of either immutable rod?
            if abs(c-start-1)+max(0,r-(start+lo-1))<=1:return (start//3)*stride
            if abs(c-start)+max(0,start+2-r)<=1:return (start//3)*stride+1
            if c==start and r-start in splits:
                return (start//3)*stride+2+splits.index(r-start)
        return (r,c)
    def fixed(r,c):
        return c==1 and r<lo or c==0 and r>=2 or c==3 and r>=5
    cells=list(product(range(lo,hi+1),(1,2)))
    base=max(0,1-lo)+1  # removed tail of A plus one old satellite
    terminals=2*stride
    names={i:i for i in range(terminals)}
    bundles=[]
    for r,c in cells:
        edges=[]
        for x,y in ((r-1,c),(r+1,c),(r,c-1),(r,c+1)):
            if fixed(x,y):continue
            a,b=label(r,c),label(x,y)
            u=names.setdefault(a,len(names));v=names.setdefault(b,len(names))
            edges.append((tuple(sorted(((r,c),(x,y)))),u,v))
        bundles.append(edges)
    best={}
    for mask in range(1<<len(cells)):
        parent=list(range(len(names)))
        def root(x):
            while x!=parent[x]:x=parent[x]
            return x
        ok=True;seen=set()
        for j,bundle in enumerate(bundles):
            if not mask>>j&1:continue
            for key,u,v in bundle:
                if key in seen:continue
                seen.add(key)
                a,b=root(u),root(v)
                if a==b:ok=False;break
                parent[a]=b
            if not ok:break
        if ok:
            sig=canonical(root(t) for t in range(terminals))
            if sig not in best or best[sig][0]<mask.bit_count()-base:
                best[sig]=(mask.bit_count()-base,mask)
    return stride,best,cells


def audit(lo=-1,hi=4):
    # Recompute each pocket by explicitly constructing its surrounding
    # stars in physical coordinates, without the analytic root labels.
    stride,pk,cells=packets(lo,hi)
    fixed={(r,1) for r in range(-12,lo)}|{(r,4) for r in range(-12,lo+3)}
    fixed|={(r,0) for r in range(2,14)}|{(r,3) for r in range(5,14)}
    ports=[]
    for j in (0,3):
        ports.extend([(-12,j+1),(13,j),*((r+j,j) for r in range(lo,1))])
    def edges(S):
        return {tuple(sorted(((r,c),(r+x,c+y)))) for r,c in S for x,y in ((1,0),(-1,0),(0,1),(0,-1))}
    baseline=edges(fixed)
    def summarize(centers):
        e=baseline|edges(centers)
        adj={p:[] for p in ports}
        for a,b in e:
            adj.setdefault(a,[]).append(b);adj.setdefault(b,[]).append(a)
        comp={}
        for x in adj:
            if x in comp:continue
            q=[x];comp[x]=x
            while q:
                for y in adj[q.pop()]:
                    if y not in comp:comp[y]=x;q.append(y)
        if len(e)+len(set(comp.values()))!=len(adj):return
        return canonical(comp[p] for p in ports)
    best={}
    for mask in range(1<<len(cells)):
        chosen={x for j,x in enumerate(cells) if mask>>j&1}
        sig=summarize(chosen)
        if sig is not None:best[sig]=max(best.get(sig,-999),len(chosen)-(2-lo))
    assert best=={sig:score for sig,(score,_) in pk.items()}
    print("physical-grid replay:",1<<len(cells),"masks,",len(best),"signature maxima agree")


def split_control():
    from .nested_renewal import direct_q,ledger
    n=14
    q=direct_q(n)
    f=(q-{r*n+3 for r in (6,7,8)})|{r*n+4 for r in (5,7)}
    assert ledger(n,f)["forest"]
    def connected(F):
        seen={7};todo=[7]
        while todo:
            i=todo.pop()
            for j in (i-1,i+1,i-n,i+n):
                if 0<=j<n*n and abs(i%n-j%n)<=1 and j not in seen and (i in F or j in F):
                    seen.add(j);todo.append(j)
        return 13*n+3 in seen
    assert connected(q) and not connected(f)
    print("two-column physical edit:",len(q),"->",len(f),"forest; top 7 and bottom 3 now separated")


def rod_packets(lo=-1,hi=4):
    """Both rod tips free, physical separator column retains its satellite."""
    assert lo<=0 and hi>=2
    cells=list(product(range(lo,hi+1),(0,1)))
    fixed={(-1,-1),(2,2)}
    for j in (-1,0,1):
        fixed|={(r,3*j+1) for r in range(-18,3*j+lo)}
        fixed|={(r,3*j) for r in range(3*j+hi+1,19)}
    dirs=((-1,0),(1,0),(0,-1),(0,1))
    def stars(points):
        return {tuple(sorted(((r,c),(r+x,c+y)))) for r,c in points for x,y in dirs}
    fixed_edges=stars(fixed)
    nodes={}
    def node(x):
        return nodes.setdefault(x,len(nodes))
    ee=[(node(a),node(b)) for a,b in fixed_edges]
    # Left separator: prev top, current bottom, plus every non-rod
    # separator site not already in one of those rods' fixed star support.
    ports=[]
    for j in (0,3):
        ports.extend([node((-18,j-2)),node((18,j)),*(node((r+j,j-1)) for r in range(lo-3,hi+1))])
    stride=len(ports)//2
    bundles=[[(node(a),node(b)) for a,b in stars([p])-fixed_edges] for p in cells]
    parent=list(range(len(nodes)))
    def root(x):
        while parent[x]!=x:x=parent[x]
        return x
    for a,b in ee:
        x,y=root(a),root(b)
        assert x!=y
        parent[x]=y
    best={}
    base=1-lo+hi-1 # removed A tail and B head, satellite remains
    def visit(i,mask,seen):
        if i==len(cells):
            sig=canonical(root(x) for x in ports)
            v=mask.bit_count()-base
            if sig not in best or v>best[sig][0]:best[sig]=v,mask
            return
        visit(i+1,mask,seen)
        added=[]
        for edge in bundles[i]:
            if edge in seen:continue
            a,b=map(root,edge)
            if a==b:break
            parent[a]=b;added.append(a)
        else:visit(i+1,mask|1<<i,seen|set(bundles[i]))
        for x in reversed(added):parent[x]=x
    visit(0,0,set())
    return stride,best,cells


def symbolic_blocks(lo,hi,num,rods=False):
    stride,pk,_=(rod_packets if rods else packets)(lo,hi)
    if rods:
        # Each broken B_j -- satellite_j -- A_(j+1) path needs at
        # least one missing incidence. Charge both incidences if both
        # are absent; sum actual split count is <= this charge.
        sat=2+(-1-(lo-3))
        maxima={}
        for sig,(gain,_) in pk.items():
            a=sig[sat]==sig[stride]
            b=sig[stride+sat]==sig[1]
            maxima[a,b]=max(maxima.get((a,b),-999),gain)
        print("best delta by retained left/right satellite incidences",maxima,flush=True)
        if all(gain<=-int(not a)-int(not b) for (a,b),gain in maxima.items()) and len(pk)>100:
            from .modified_crop import solve
            vec=solve(1,blocks=5)
            assert vec[-1]=={s:v+7 for s,v in vec[-2].items()}
            print("net <= frame - splits; exact paid-split vector shift 7 on",
                  len(vec[-1]),"states",flush=True)
            return
    # A finer partition at no lower score cannot create a cycle that
    # a coarser one avoids. It also leaves at least as much freedom for
    # every later pocket. Use dominance only within identical fixed ports.
    def connections(sig):
        return sum(1<<(i*len(sig)+j) for i,p in enumerate(sig)
                   for j in range(i) if p==sig[j])
    kept=[]
    for sig,(gain,mask) in sorted(pk.items(),key=lambda kv:(-kv[1][0],connections(kv[0]).bit_count())):
        bits=connections(sig)
        if not any((b&bits)==b for _,_,b in kept):
            kept.append((sig,(gain,mask),bits))
    print("undominated pocket signatures",len(kept),flush=True)
    if rods and len(pk)>100:
        pk={sig:p for sig,p,_ in kept}
    # Current six frame positions, left ports and right ports. Add right
    # ports when a block begins; forget left ones only after all joins.
    @lru_cache(None)
    def frame(ph,s,m):
        old,part=s;parent=list(range(max(part)+8))
        def root(x):
            while parent[x]!=x:x=parent[x]
            return x
        def add(a,b):
            a,b=root(a),root(b)
            if a==b:return False
            parent[a]=b;return True
        cur=[max(part)+1+i for i in range(6)]
        for i in range(6):
            if (old|m)&(1<<i) and not add(part[i],cur[i]):return
            if i%3 and (m>>(i-1))&3 and not add(cur[i-1],cur[i]):return
        if (ph==1 or m&1) and not add(cur[0],part[6+stride*rods]):return
        if (ph==0 or m&8) and not add(cur[3],part[7+stride*(ph==2)]):return
        return m,canonical(root(x) for x in cur+list(part[6:]))

    @lru_cache(None)
    def join(part,sig):
        parent=list(range(max(part)+1))
        def root(x):
            while parent[x]!=x:x=parent[x]
            return x
        for t,c in enumerate(sig):
            # Fixed satellite stars at both separators were included in
            # the previous packet too. Identify their three adjacent
            # vertical sites exactly once, on first encounter. The other
            # two leaves of each fixed star are interior to a packet.
            if rods and t<stride and t>=2 and (t-2+lo-3) in (-1,0):
                continue
            if sig.index(c)==t:continue
            a,b=root(part[6+t]),root(part[6+sig.index(c)])
            if a==b:return
            parent[a]=b
        short=canonical(root(x) for x in part[:6]+part[6+stride:])
        return short+tuple(range(max(short)+1,max(short)+1+stride))

    init=list(range(6+2*stride))
    if rods:
        first=6+2+(-2-(lo-3))
        init[first+1]=init[first+2]=init[first]
    d={(0,canonical(init)):0}
    snaps=[]
    for j in range(num):
        for ph in range(3):
            nd={}
            for s,v in d.items():
                for m in range(64):
                    t=frame(ph,s,m)
                    if t is not None:nd[t]=max(nd.get(t,-9999),v+m.bit_count())
            d=nd
        nd={}
        for (mask,part),v in d.items():
            for sig,(gain,_) in pk.items():
                p=join(part,sig)
                if p is not None:nd[mask,p]=max(nd.get((mask,p),-9999),v+gain)
        d=nd
        print("block",j+1,"states",len(d),"paired frame + core delta",max(d.values()),flush=True)
        for i,prior in enumerate(snaps):
            if prior.keys()==d.keys():
                diffs={v-prior[k] for k,v in d.items()}
                if len(diffs)==1:
                    print("vector recurrence:",j-i,"blocks,",diffs.pop(),"centers",flush=True)
                    return
        snaps.append(d)


if __name__=='__main__':
    import sys
    lo,hi=map(int,sys.argv[1:3]) if len(sys.argv)>2 else (-1,4)
    rods='--rods' in sys.argv
    stride,pk,cells=(rod_packets if rods else packets)(lo,hi)
    print("cells",len(cells),"ports per cut",stride,"feasible signatures",len(pk),
          "best isolated delta",max(x[0] for x in pk.values()),flush=True)
    split_control()
    symbolic_blocks(lo,hi,10,rods)
