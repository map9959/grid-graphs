"""Exact four-row event inequality and period-three upper-model test."""
from collections import Counter
from .four_row_separator import probabilities,advance,masks,Q,Path,json
from .patch_square import MASKS,SYM,trans
from .repeating_patch_dual import polynomial,verify,filename


def special(n):
    return {(1,0,258),(1,0,288),(1,1,132),(n-4,0,66),(n-3,0,292)}


def front(states,j,ok):
    return {d for s in states for c in range(16)
            if (j<2 or all(m in ok[r] for r,m in enumerate(masks(*s[:2],c))))
            and (d:=advance(s,c)) is not None}


def template():
    # Read a compact representative on the smallest side of the depth-five model.
    p=probabilities(25)
    return [[set(p(6+r,j)) for r in range(2)] for j in range(23)]


def maps(n,j,T):
    S=n-2
    x=j if j<7 else 23+j-S if j>=S-7 else 7+(j-7)%3
    return T[x]


def replay_cover():
    T=template()
    for n in (25,28,109):
        p=probabilities(n);exc=special(n);s={(0,0,(0,1,2,3))};seen={}
        for j in range(n):
            ok=[set(),set()]
            if j>=2:
                ok=maps(n,j-2,T)
                assert all(ok[r]==p(6+r,j-2).keys() for r in range(2))
                ok=[ms-{m for c,h,m in exc if c==j-2 and h==r} for r,ms in enumerate(ok)]
            s=front(s,j,ok);seen[j]=s
        assert not s
        # After column 11, an extra triplet repeats exactly the same
        # frontier before consuming the remainder of the representative.
        assert seen[11]==seen[14] and seen[11]
        assert all(maps(n,j-2,T)==maps(n,j+1,T) for j in (12,13,14))
        vals=[p(6+r,c)[m] for c,r,m in sorted(exc)]
        assert sum(vals)==Q(67,72)
        print('side',n,'periodic frontier states',len(seen[11]),'terminal avoiding states',len(s),
              'cover LHS',sum(vals),'required >= 1')


def row(n,ns,T):
    # Pooled variables at depth 5 are per-fine-type sums (patch depth 8).
    # For each labeled fine position use its row once, not once per copy.
    D=8;S=n-2
    ax=lambda i:i if i<D else 2*D+3+i-S if i>=S-D else D+(i-D)%3
    exc=special(n);c=Counter();done={}
    for j in range(S):
        for r,ms in enumerate(maps(n,j,T)):
            charged=frozenset(m for m in MASKS if m not in ms or (j,r,m) in exc)
            key=r,ax(j)
            if key in done:assert charged==done[key];continue
            done[key]=charged
            ps=[tuple(map(ax,trans(6+r,j,S,g))) for g in range(8)]
            for m in charged:c[ns['p',min(zip(ps,SYM[m]))]]+=1
    return tuple(sorted(c.items()))


def pinned_reports(n,ns):
    """Both top-strip patches report the bit at physical site (2,6)."""
    S=n-2
    def ax(i):return i if i<8 else 19+i-S if i>=S-8 else 8+(i-8)%3
    reports=[]
    for j in (5,6):
        c=Counter()
        assert sum(ax(z)==ax(j) for z in range(S))==1
        ps=[tuple(map(ax,trans(0,j,S,g))) for g in range(8)]
        for m in MASKS:
            if (m>>(3*2+(6-j)))&1:c[ns['p',min(zip(ps,SYM[m]))]]+=1
        reports.append(c)
    return reports


def pinned_overlap(n,ns):
    left,right=pinned_reports(n,ns)
    left.subtract(right)
    return tuple(sorted((x,w) for x,w in left.items() if w))


def test(replay,pinned=False):
    d=5;n,ns,A,b,obj=polynomial(d,3,1);T=template()
    r=row(n,ns,T)
    assert r==row(n+3,ns,T)==row(109,ns,T)
    A.append((r,'>='));b.append((1,0,0))
    path=Path(__file__).with_name('four_cover_d5_primal.json')
    sep=pinned_overlap(n,ns)
    assert sep==pinned_overlap(109,ns)
    if pinned:
        A.append((sep,'='));b.append((0,0,0))
        path=path.with_name('four_cover_pinned_d5_primal.json')
    _,pairs=json.loads(filename(5,3,1).read_text())
    y={i:Q(v) for i,v in pairs}
    assert verify(A,obj,y)<=0
    coeff=[sum(v*b[i][j] for i,v in y.items()) for j in range(3)]
    h=28;rhs=[v+w*h+z*h*(h-1)//2 for v,w,z in b]
    if replay:p={x:Q(v) for x,v in json.loads(path.read_text()).items()}
    else:
        from .side28_score import solve
        _,_,v=solve(A,rhs,obj,ns)
        p={x:Q(float(w)).limit_denominator(1000000) for x,w in v.items() if w>1e-9}
        piv={}
        for ((cs,op),bb) in zip(A,rhs):
            if op!='=' and abs(sum(v[x]*w for x,w in cs)-bb)>1e-7:continue
            c={x:Q(w) for x,w in cs if x in p};bb=Q(bb)
            while c:
                x=min(c);w=c.pop(x)
                if x not in piv:piv[x]=({z:k/w for z,k in c.items()},bb/w);break
                pc,base=piv[x];bb-=w*base
                for z,k in pc.items():
                    c[z]=c.get(z,0)-w*k
                    if not c[z]:del c[z]
        for x,(c,bb) in sorted(piv.items(),reverse=True):p[x]=bb-sum(w*p[z] for z,w in c.items())
    assert set(p)<=set(ns.values()) and min(p.values())>=0
    for ((cs,op),bb) in zip(A,rhs):
        z=sum(w*p.get(x,0) for x,w in cs)-bb
        assert {'=':z==0,'<=':z<=0,'>=':z>=0}[op]
    score=sum(w*p.get(x,0) for x,w in obj.items())
    assert score==sum(v*rhs[i] for i,v in y.items())
    print('verified columns',len(ns),'Newton upper in (n-25)/3',*[str(z) for z in coeff])
    print('side',25+3*h,'strengthened pooled optimum',score,'cover lhs',sum(w*p.get(x,0) for x,w in r))
    gap=sum(w*p.get(x,0) for x,w in sep)
    assert gap==(0 if pinned else Q(15,46))
    vals=[sum(w*p.get(x,0) for x,w in report.items()) for report in pinned_reports(109,ns)]
    assert vals[0]-vals[1]==gap
    print('top strip: Pr((2,6) selected) left',vals[0],'right',vals[1],'difference',gap,'required = 0')
    if not replay:path.write_text(json.dumps({x:str(v) for x,v in p.items()},separators=(',',':'))+'\n')


if __name__=='__main__':
    import sys
    replay_cover()
    if '--test' in sys.argv or '--replay' in sys.argv:test('--replay' in sys.argv,'--pinned' in sys.argv)
