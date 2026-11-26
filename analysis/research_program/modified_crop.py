"""Adaptive core-link cuts, comparing raw and net frame capacity."""
from functools import lru_cache
from .crop_frame_rate import canonical,step,graph_step


@lru_cache(None)
def leaf_choices(g,h):
    """a_j=3j; B_j starts at a_j+2+g. Rows relative to a_j."""
    options={}
    for mask in range(1<<(2+h)):
        rs=[2+i for i in range(2+h) if mask>>i&1]
        right=sum(r<=3 for r in rs)   # A_(j+1) at horizontal distance 2
        left=sum(r>=2+g for r in rs)  # B_j at horizontal distance 2
        if max(right,left)>1:continue
        linked=bool(right and left)
        options[linked]=max(options.get(linked,-100),len(rs)-1-g)
    return options


@lru_cache(None)
def packet(g,h,rise):
    # Translate the left top endpoint to row zero. The next top
    # endpoint is at rise; the two bottom start rows are 2+g
    # and rise+2+h. All candidates are in a single intervening column.
    options={}
    length=max(0,rise+h-1)
    for mask in range(1<<length):
        rs=[i+2 for i in range(length) if mask>>i&1]
        clusters=[]
        for r in rs:
            if not clusters or r-clusters[-1][-1]>2:clusters.append([])
            clusters[-1].append(r)
        links=0
        for cluster in clusters:
            rt=sum(r<=rise for r in cluster)
            lt=sum(r>=2+g for r in cluster)
            if max(rt,lt)>1:break
            links+=int(bool(rt and lt))
        else:
            if links<=1:
                key=bool(links)
                options[key]=max(options.get(key,-999),len(rs)-1-g)
    return options


def local_rate(gaps,shifts):
    # Even giving the paired frame its full 8 centers per triple, the
    # core must not lose any score on average to attain the target.
    types=[(g,u) for g in gaps for u in shifts]
    opts={}
    for g,u in types:
        for h,v in types:
            for link,delta in packet(g,h,3+v-u).items():
                opts[g,u,h,v,link]=delta
    return types,opts


def potential():
    # For shifts -2..2 and gap extras 0..3 the packet charge
    # 2*delta + split is <= 3/5 per step plus a potential difference.
    types,opts=local_rate(range(4),range(-2,3))
    height={x:0 for x in types}
    for _ in types:
        for (g,u,h,v,link),delta in opts.items():
            w=5*(2*delta+int(not link))-3
            height[h,v]=max(height[h,v],height[g,u]+w)
    for (g,u,h,v,link),delta in opts.items():
        assert 5*(2*delta+int(not link))-3<=height[h,v]-height[g,u]
    return height,len(opts)


def physical():
    from .nested_renewal import direct_q,ledger
    n=14;orig=direct_q(n)
    # Shorten B_2 by one. Replace packet 1's singleton with a lower
    # leaf, and then enumerate packet 2. Use zero-based crop coordinates.
    score=[]
    for g in (0,1):
        for h in (0,1):
            base=orig-{(5*n+5)}
            if g:base.discard(5*n+3)
            if h:base.discard(8*n+6)
            for subset in range(1<<(2+h)):
                F=base|{(5+i)*n+5 for i in range(2+h) if subset>>i&1}
                report=ledger(n,F)
                score.append(report["forest"])
    assert any(score) and not all(score)
    # Actually separate the two ports with a neutral packet (g,h)=(0,1).
    # The next packet pays the outstanding rod shortening.
    F=(orig-{5*n+5,8*n+6})|{7*n+5}
    assert ledger(n,F)["forest"] and len(F)==len(orig)-1
    def joined(chosen):
        start=7  # A_2 top
        seen={start};q=[start]
        while q:
            a=q.pop()
            for b in (a+1,a-1,a+n,a-n):
                if (0<=b<n*n and abs(a%n-b%n)<=1 and b not in seen and
                        (a in chosen or b in chosen)):
                    q.append(b);seen.add(b)
        return (n-1)*n+3 in seen
    assert joined(orig) and not joined(F)
    print("n14 pinch test: 69 ->",len(F),"centers; forest; top 7 and bottom 3 disconnected",
          "local placements checked",len(score))


def trim_test(check=False):
    # Start anywhere in the interior. Both possible initial trims are
    # permitted. Never charge an unprocessed terminal packet for its trim.
    init=(0,tuple(range(9)))
    d={(init,g):0 for g in range(2)}
    snaps=[]
    trans=lru_cache(None)(graph_step) if check else step
    for i in range(18):
        nd={}
        for (s,g),v in d.items():
            for m in range(64):
                t=trans(False,i%3,s,m)
                if t is None:continue
                score=v+m.bit_count()
                if i%3!=2:
                    nd[t,g]=max(nd.get((t,g),-999),score)
                    continue
                for h in (0,1):
                    for link,delta in leaf_choices(g,h).items():
                        p=list(t[1])
                        if not link:p[6]=max(p)+1
                        key=(m,canonical(p)),h
                        nd[key]=max(nd.get(key,-999),score+delta)
        d=nd
        if i%3==2:snaps.append(d)
    return snaps


def solve(cost,check=False,blocks=7):
    d={(0,tuple(range(9))):0}
    nxt=lru_cache(None)(graph_step) if check else step
    snapshots=[]
    for i in range(3*blocks):
        nd={}
        for s,v in d.items():
            for m in range(64):
                t=nxt(False,i%3,s,m)
                if t is None:continue
                w=v+m.bit_count()
                nd[t]=max(nd.get(t,-1000),w)
                if i%3==2:
                    # Replace the incoming top port by a separate root.
                    # The former bottom root's connections to the *past*
                    # are retained in the partition of the other slots.
                    p=list(t[1]);p[6]=max(p)+1
                    split=m,canonical(p)
                    nd[split]=max(nd.get(split,-1000),w-cost)
        d=nd
        if i%3==2:snapshots.append(d)
    return snapshots


if __name__=='__main__':
    for c in (0,.5,1):
        a=solve(c,blocks=5)
        assert a==solve(c,True,blocks=5)
        rate=8-c
        assert a[-1]=={s:v+rate for s,v in a[-2].items()}
        print("cut charge",c,[(len(d),max(d.values())) for d in a],"uniform shift",rate)
    print("trim/next trim -> {linked: maximum core delta}",{(g,h):leaf_choices(g,h) for g in (0,1) for h in (0,1)})
    a=trim_test()
    assert a==trim_test(True)
    assert a[-1]=={s:v+15 for s,v in a[-3].items()}
    print("trim and promotion, net paired maxima",[(len(d),max(d.values())) for d in a])
    for lag in (1,2):
        print("last shifts with lag",lag,sorted({v-a[-lag-1][s] for s,v in a[-1].items()}))
    pot,count=potential()
    print("shift/trim certificate:",len(pot),"types,",count,"inequalities, potential range",
          (min(pot.values()),max(pot.values())),"paired net rate <= 39/5")
    physical()
