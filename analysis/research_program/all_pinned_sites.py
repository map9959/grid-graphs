"""Single-bit agreement on every adjacent pair of singleton fine patch positions."""
from functools import lru_cache
from itertools import product
from .repeating_four_cover import polynomial,template,row,pinned_overlap,MASKS,SYM,trans,Counter,Q,Path,json,verify


def agreements(n,ns,joint=False):
    S=n-2
    def ax(i):return i if i<8 else 19+i-S if i>=S-8 else 8+(i-8)%3
    freq=Counter(ax(i) for i in range(S))
    pinned={i for i in range(S) if freq[ax(i)]==1}
    @lru_cache(None)
    def atoms(i,j):
        pos=[tuple(map(ax,trans(i,j,S,g))) for g in range(8)]
        return [(m,ns['p',min(zip(pos,SYM[m]))]) for m in MASKS]
    @lru_cache(None)
    def bit(i,j,u,v):
        return Counter(x for m,x in atoms(i,j) if m>>(3*u+v)&1)
    unique=set();pairs=0
    for i,j in product(sorted(pinned),repeat=2):
        for di,dj in ((0,1),(1,0)):
            if i+di not in pinned or j+dj not in pinned:continue
            pairs+=1
            cells=list(product(range(di,3),range(dj,3)))
            if joint:
                diffs=[Counter() for _ in range(64)]
                for a,b,sign in ((0,0,1),(di,dj,-1)):
                    for m,x in atoms(i+a,j+b):
                        k=sum(((m>>(3*(u-a)+v-b))&1)<<h for h,(u,v) in enumerate(cells))
                        diffs[k][x]+=sign
            else:
                diffs=[]
                for u,v in cells:
                    c=bit(i,j,u,v).copy()
                    c.subtract(bit(i+di,j+dj,u-di,v-dj))
                    diffs.append(c)
            for c in diffs:
                cs=tuple(sorted((x,w) for x,w in c.items() if w))
                if cs:unique.add(cs if cs[0][1]>0 else tuple((x,-w) for x,w in cs))
    assert pairs==448
    return sorted(unique)


def primal(A,rhs,v):
    p={x:Q(float(w)).limit_denominator(1000000) for x,w in v.items() if w>1e-9}
    piv={}
    for (row,op),b in zip(A,rhs):
        if op!='=' and abs(sum(v[x]*w for x,w in row)-b)>1e-7:continue
        c={x:Q(w) for x,w in row if x in p};b=Q(b)
        while c:
            x=min(c);w=c.pop(x)
            if x not in piv:piv[x]=({z:k/w for z,k in c.items()},b/w);break
            pc,q=piv[x];b-=w*q
            for z,k in pc.items():
                c[z]=c.get(z,0)-w*k
                if not c[z]:del c[z]
    for x,(c,b) in sorted(piv.items(),reverse=True):p[x]=b-sum(w*p[z] for z,w in c.items())
    return p


def run(replay,joint=False):
    n,ns,A,b,obj=polynomial(5,3,1)
    A.extend([(row(n,ns,template()),'>='),(pinned_overlap(n,ns),'=')]);b.extend([(1,0,0),(0,0,0)])
    eqs=agreements(109,ns,joint);assert eqs==agreements(n,ns,joint)
    prev=json.loads(Path(__file__).with_name('all_pinned_sites_109.json' if joint else 'four_cover_pinned_d5_primal.json').read_text())
    old={x:Q(q) for x,q in (prev[0] if joint else prev).items()}
    violations=[abs(sum(w*old.get(x,0) for x,w in cs)) for cs in eqs]
    print('448 adjacent pairs;',448*(64 if joint else 6),'physical comparisons;',len(eqs),'distinct nonzero rows;',
          sum(v>0 for v in violations),'violated by previous optimizer; max',max(violations),flush=True)
    for cs in eqs:A.append((cs,'='));b.append((0,0,0))
    rhs=[v+28*w+378*z for v,w,z in b]
    path=Path(__file__).with_name('all_pinned_joint_109.json' if joint else 'all_pinned_sites_109.json')
    if replay:
        pp,yy=json.loads(path.read_text());p={x:Q(w) for x,w in pp.items()};y={int(i):Q(w) for i,w in yy.items()}
    else:
        from .side28_score import solve
        opt,raw,v=solve(A,rhs,obj,ns);print('candidate optimum',opt,flush=True)
        p=primal(A,rhs,v)
        y={i:Q(float(w)).limit_denominator(10**6) for i,w in enumerate(raw) if abs(w)>1e-9}
        if verify(A,obj,y)>0:
            from .repeating_patch_dual import recover
            y=recover(A,obj,{i:Q(float(w)) for i,w in enumerate(raw) if abs(w)>1e-9})
    assert p.keys()<=set(ns.values()) and min(p.values())>=0
    for (cs,op),bb in zip(A,rhs):
        z=sum(w*p.get(x,0) for x,w in cs)-bb
        assert {'=':z==0,'<=':z<=0,'>=':z>=0}[op]
    score=sum(w*p.get(x,0) for x,w in obj.items())
    print('verified primal',score,flush=True)
    assert verify(A,obj,y)<=0
    coeff=[sum(q*b[i][j] for i,q in y.items()) for j in range(3)]
    upper=sum(q*rhs[i] for i,q in y.items())
    assert score==upper
    print('exact pooled optimum',score,'previous minus new',(Q(3793203583,925484) if joint else Q(1225659,299))-score)
    print('repeating upper Newton coefficients in (n-25)/3:',*[str(q) for q in coeff])
    if not replay:path.write_text(json.dumps([{x:str(w) for x,w in p.items()},{i:str(w) for i,w in y.items()}],separators=(',',':'))+'\n')


if __name__=='__main__':
    import sys
    run('--replay' in sys.argv,'--joint' in sys.argv)
