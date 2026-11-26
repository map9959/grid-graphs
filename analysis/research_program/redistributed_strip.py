"""Strip overlaps summed across unpinned columns, without tying physical marginals."""
from functools import lru_cache
from .all_pinned_sites import agreements,primal
from .repeating_four_cover import polynomial,template,row,pinned_overlap,MASKS,SYM,trans,Counter,Q,Path,json,verify


def cuts(n,ns):
    S=n-2
    def ax(j):return j if j<8 else 19+j-S if j>=S-8 else 8+(j-8)%3
    phases={ax(j):j for j in range(8,S-8)}
    @lru_cache(None)
    def projections(i,j,shift):
        pos=[tuple(map(ax,trans(i,j,S,g))) for g in range(8)]
        out=[Counter() for _ in range(64)]
        for m in MASKS:
            out[(m>>shift)&63][ns['p',min(zip(pos,SYM[m]))]]+=1
        return out
    unique=set();special=None
    for i in range(7):
        for phase,j in phases.items():
            # A pooled variable is already a SUM over these columns,
            # not the probability of the event at the representative j.
            top=projections(i,j,3)
            bottom=projections(i+1,j,0)
            for word in range(64):
                c=top[word].copy();c.subtract(bottom[word])
                cs=tuple(sorted((x,w) for x,w in c.items() if w))
                if i==5 and phase==8 and word==0:
                    special=top[word],bottom[word]
                if cs:unique.add(cs if cs[0][1]>0 else tuple((x,-w) for x,w in cs))
    assert special is not None
    return sorted(unique),special


def run(replay):
    n,ns,A,b,obj=polynomial(5,3,1)
    A.extend([(row(n,ns,template()),'>='),(pinned_overlap(n,ns),'=')]);b.extend([(1,0,0),(0,0,0)])
    for cs in agreements(n,ns,True):A.append((cs,'='));b.append((0,0,0))
    eqs,ends=cuts(109,ns);assert (eqs,ends)==cuts(n,ns)
    prev,_=json.loads(Path(__file__).with_name('all_pinned_joint_109.json').read_text())
    old={x:Q(v) for x,v in prev.items()}
    sums=[sum(w*old.get(x,0) for x,w in cs.items()) for cs in ends]
    assert sums==[Q(1,42),0]
    bad=sum(sum(w*old.get(x,0) for x,w in cs)!=0 for cs in eqs)
    print('strip rows 5..8, shared 2x3 all-zero event: phase sums',*sums,'required equal',flush=True)
    print(len(eqs),'distinct pooled equations;',bad,'violations',flush=True)
    for cs in eqs:A.append((cs,'='));b.append((0,0,0))
    rhs=[v+28*w+378*z for v,w,z in b]
    path=Path(__file__).with_name('redistributed_strip_109.json')
    if replay:
        pp,yy=json.loads(path.read_text());p={x:Q(v) for x,v in pp.items()};y={int(i):Q(v) for i,v in yy.items()}
    else:
        from .side28_score import solve
        opt,raw,v=solve(A,rhs,obj,ns);print('candidate optimum',opt,flush=True)
        p=primal(A,rhs,v)
        y={i:Q(float(v)).limit_denominator(10**6) for i,v in enumerate(raw) if abs(v)>1e-9}
        if verify(A,obj,y)>0:
            from .repeating_patch_dual import recover
            y=recover(A,obj,{i:Q(float(w)) for i,w in enumerate(raw) if abs(w)>1e-9})
    assert p.keys()<=set(ns.values()) and min(p.values())>=0
    for (cs,op),bb in zip(A,rhs):
        z=sum(w*p.get(x,0) for x,w in cs)-bb
        assert {'=':z==0,'<=':z<=0,'>=':z>=0}[op]
    score=sum(w*p.get(x,0) for x,w in obj.items())
    assert verify(A,obj,y)<=0 and score==sum(v*rhs[i] for i,v in y.items())
    coeff=[sum(q*b[i][j] for i,q in y.items()) for j in range(3)]
    print('verified optimum',score,'integer upper',int(score),'previous minus new',Q(1118890,273)-score)
    print('repeating upper Newton coefficients',*[str(q) for q in coeff])
    if not replay:path.write_text(json.dumps([{x:str(v) for x,v in p.items()},{i:str(v) for i,v in y.items()}],separators=(',',':'))+'\n')


if __name__=='__main__':
    import sys
    run('--replay' in sys.argv)
