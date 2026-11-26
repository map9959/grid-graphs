"""Couple the whole 4 x 109 forest-path polytope to the depth-five pooled model."""
from collections import defaultdict
from .redistributed_transfer import (polynomial, row, template, pinned_overlap,
    agreements,cuts,load,certificate,data,Counter,Q,Path,json,verify,primal,axis)
from .four_row_separator import advance,masks
from functools import lru_cache
from .patch_square import MASKS,SYM,trans


@lru_cache(None)
def advance5(state,c):
    _,b,part=state
    p=list(part)+list(range(5,10))
    def root(x):
        while x!=p[x]:x=p[x]
        return x
    for u,v,on in [(r,r+5,(b|c)>>r&1) for r in range(5)]+[(5+r,6+r,(c|c>>1)>>r&1) for r in range(4)]:
        if on:
            a,z=root(u),root(v)
            if a==z:return None
            p[a]=z
    roots=[root(x) for x in range(5,10)]
    return b,c,tuple(roots.index(x) for x in roots)


@lru_cache(None)
def masks5(a,b,c):
    return tuple(sum(((w>>(r+i))&1)<<(3*i+j) for i in range(3) for j,w in enumerate((a,b,c))) for r in range(3))


def model(height=4):
    n,ns,A,b,obj=polynomial(5,3,1)
    A.extend([(row(n,ns,template()),'>='),(pinned_overlap(n,ns),'=')]);b.extend([(1,0,0),(0,0,0)])
    for cs in agreements(n,ns,True)+cuts(n,ns)[0]:A.append((cs,'='));b.append((0,0,0))
    old=load();A.append((certificate(n,ns,old),'>='));b.append((1,0,0))
    rhs=[v+28*w+378*z for v,w,z in b]
    labels,_,_=data(109,0,ns,old)
    if height==5:
        for j in range(107):
            pos=[tuple(axis(v,107) for v in trans(2,j,107,g)) for g in range(8)]
            for m in MASKS:
                key=(axis(j,107),2,m)
                x=ns['p',min(zip(pos,SYM[m]))]
                assert labels.setdefault(key,x)==x
    order=list(labels);link={k:[(labels[k],-1)] for k in order}
    balance=defaultdict(list);start=(0,0,tuple(range(height)));states={start}
    step,events=(advance5,masks5) if height==5 else (advance,masks)
    count=0
    for j in range(109):
        nxt=set()
        for s in sorted(states):
            for c in range(1<<height):
                d=step(s,c)
                if d is None:continue
                x=f'z{count}';ns['arc',count]=x;count+=1
                balance[j,s].append((x,1))
                if j<108:balance[j+1,d].append((x,-1))
                if j>=2:
                    for r,m in enumerate(events(*s[:2],c)):link[axis(j-2,107),r,m].append((x,1))
                nxt.add(d)
        states=nxt
    base=len(A)
    for k in order:A.append((tuple(link[k]),'='));rhs.append(0)
    for k,terms in sorted(balance.items()):A.append((tuple(terms),'='));rhs.append(int(k==(0,start)))
    print('all legal arcs',count,'phase-sum links',len(link),'flow balances',len(balance),flush=True)
    return ns,A,rhs,obj,base


def run(build,height=4):
    ns,A,rhs,obj,base=model(height)
    path=Path(__file__).with_name('full_top_109.json' if height==4 else 'full_top5_109.json')
    if build:
        from .side28_score import solve
        opt,raw,v=solve(A,rhs,obj,ns)
        print('solver candidate',opt,flush=True)
        p=primal(A,rhs,v)
        _,yy=json.loads(Path(__file__).with_name('redistributed_transfer_109.json').read_text())
        y={int(i):Q(w) for i,w in yy.items()}
        if abs(float(sum(q*rhs[i] for i,q in y.items()))-opt)>1e-7:
            y={i:Q(float(w)).limit_denominator(10**6) for i,w in enumerate(raw) if abs(w)>1e-9}
            if verify(A,obj,y)>0:
                from .repeating_patch_dual import recover
                y=recover(A,obj,{i:Q(float(w)) for i,w in enumerate(raw) if abs(w)>1e-9})
    else:
        pp,yy=json.loads(path.read_text());p={x:Q(v) for x,v in pp.items()};y={int(i):Q(v) for i,v in yy.items()}
    assert set(p)<=set(ns.values()) and min(p.values())>=0
    for (cs,op),bb in zip(A,rhs):
        z=sum(w*p.get(x,0) for x,w in cs)-bb
        assert {'=':z==0,'<=':z<=0,'>=':z>=0}[op]
    score=sum(w*p.get(x,0) for x,w in obj.items())
    assert verify(A,obj,y)<=0
    upper=sum(q*rhs[i] for i,q in y.items());assert upper==score
    print('exact full-strip pooled optimum',score,'integer upper',int(score),'decrease',(Q(1118890,273) if height==4 else Q(12293,3))-score)
    if build:path.write_text(json.dumps([{x:str(v) for x,v in p.items() if v},{i:str(v) for i,v in y.items() if v}],separators=(',',':'))+'\n')


if __name__=='__main__':
    import sys
    run('--build' in sys.argv,5 if '--five' in sys.argv else 4)
