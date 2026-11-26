"""Four-row forest separation with phase-total marginals, not tied site probabilities."""
from functools import lru_cache
from .redistributed_strip import *
from .strip_cover import graph,shortest


def axis(j,S):
    return j if j<8 else 19+j-S if j>=S-8 else 8+(j-8)%3


def data(n,i,ns,y):
    S=n-2;rep={axis(j,S):j for j in range(S)}
    labels={};mass={}
    for c,j in rep.items():
        for r in (0,1):
            pos=[tuple(axis(v,S) for v in trans(i+r,j,S,g)) for g in range(8)]
            for m in MASKS:
                k=c,r,m
                labels[k]=x=ns['p',min(zip(pos,SYM[m]))]
                if y.get(x,0):mass[k]=y[x]
    @lru_cache(None)
    def supported(t,j):return {m for m in MASKS if (axis(j,S),t-i,m) in mass}
    layers=graph(n,i,supported)
    pooled=[[(s,d,[(axis(j,S),r,m) for j,r,m in ev]) for s,d,ev in layer] for layer in layers]
    return labels,mass,pooled


def load():
    pp,_=json.loads(Path(__file__).with_name('redistributed_strip_109.json').read_text())
    return {x:Q(v) for x,v in pp.items()}


def find():
    import highspy as H
    from .patch_square import relaxation
    ns,_,_=relaxation(25,9,pooled=5,period=3);p=load()
    for i in range(7):
        _,mass,g=data(109,i,ns,p)
        if not g[-1]:
            print('no supported forest',i);return i,{}
        for bulk in (False,True):
            ev=[k for k in mass if bulk or not 8<=k[0]<=10];ids={k:a for a,k in enumerate(ev)}
            h=H.Highs();h.setOptionValue('output_flag',False);h.setOptionValue('threads',1)
            h.addVars(len(ev),[0.]*len(ev),[1.]*len(ev))
            h.changeColsCost(len(ev),list(range(len(ev))),[float(mass[k]) for k in ev])
            while True:
                h.run()
                if h.getModelStatus()!=H.HighsModelStatus.kOptimal or h.getObjectiveValue()>=.999999:break
                y={k:Q(float(w)).limit_denominator(100000) for k,w in zip(ev,h.getSolution().col_value) if w>1e-9}
                v,path=shortest(g,y)
                if v>=1:
                    lhs=sum(w*mass[k] for k,w in y.items())
                    assert lhs<1
                    print('strip origin',i,'LHS',lhs,'cover',y,flush=True)
                    return i,y
                terms=Counter(ids[k] for k in path if k in ids)
                if not terms:break
                h.addRow(1,H.kHighsInf,len(terms),list(terms),list(terms.values()))
        print('completed strip',i,flush=True)


SPECIAL={(1,1,256),(3,1,32),(3,1,384),(4,1,384),(14,1,16),(14,1,192),(15,1,192),(16,1,192)}


def certificate(n,ns,p,cycles=True):
    from .four_row_separator import advance,masks
    labels,mass,_=data(n,0,ns,p)
    # Support outside the exhibited point is not constrained; charge its
    # complement unit cost instead. Test whether a zero-cost path exists.
    cs=Counter()
    for k,x in labels.items():
        if k not in mass or k in SPECIAL:cs[x]+=1
    s={(0,0,(0,1,2,3))};seen={}
    for j in range(n):
        nd=set()
        for u in s:
            for c in range(16):
                if j>=2:
                    ev=[(axis(j-2,n-2),r,m) for r,m in enumerate(masks(*u[:2],c))]
                    if any(k not in mass or k in SPECIAL for k in ev):continue
                v=advance(u,c) if cycles else (u[1],c,(0,1,2,3))
                if v is not None:nd.add(v)
        s=nd;seen[j]=s
    if cycles:
        assert not s and seen[12]==seen[15]
    print('width',n,'cycle check',cycles,'bulk frontier sizes',len(seen[12]),len(seen[15]),'end states',len(s))
    return tuple(sorted(cs.items()))


def replay(build=False):
    n,ns,A,b,obj=polynomial(5,3,1)
    A.extend([(row(n,ns,template()),'>='),(pinned_overlap(n,ns),'=')]);b.extend([(1,0,0),(0,0,0)])
    for cs in agreements(n,ns,True)+cuts(n,ns)[0]:A.append((cs,'='));b.append((0,0,0))
    old=load()
    cs=certificate(n,ns,old)
    assert cs==certificate(109,ns,old)
    certificate(109,ns,old,False)
    violation=sum(w*old.get(x,0) for x,w in cs)
    assert violation==Q(19,42)
    print('saved objective',sum(w*old.get(x,0) for x,w in obj.items()),'cover LHS',violation,'required >= 1',flush=True)
    A.append((cs,'>='));b.append((1,0,0));rhs=[v+28*w+378*z for v,w,z in b]
    path=Path(__file__).with_name('redistributed_transfer_109.json')
    if build:
        from .side28_score import solve
        opt,raw,v=solve(A,rhs,obj,ns);print('new numerical candidate',opt,flush=True)
        p=primal(A,rhs,v)
        _,joined=json.loads(Path(__file__).with_name('redistributed_strip_109.json').read_text())
        y={int(i):Q(w) for i,w in joined.items()}
        if abs(float(sum(v*rhs[i] for i,v in y.items()))-opt)>1e-7:
            y={i:Q(float(v)).limit_denominator(10**6) for i,v in enumerate(raw) if abs(v)>1e-9}
            if verify(A,obj,y)>0:
                from .repeating_patch_dual import recover
                y=recover(A,obj,{i:Q(float(w)) for i,w in enumerate(raw) if abs(w)>1e-9})
    else:
        pp,yy=json.loads(path.read_text());p={x:Q(v) for x,v in pp.items()};y={int(i):Q(v) for i,v in yy.items()}
    assert p.keys()<=set(ns.values()) and min(p.values())>=0
    for (row_,op),bb in zip(A,rhs):
        z=sum(w*p.get(x,0) for x,w in row_)-bb
        assert {'=':z==0,'<=':z<=0,'>=':z>=0}[op]
    score=sum(w*p.get(x,0) for x,w in obj.items())
    assert verify(A,obj,y)<=0 and score==sum(v*rhs[i] for i,v in y.items())
    print('exact new optimum',score,'cover lhs',sum(w*p.get(x,0) for x,w in cs),'integer upper',int(score))
    if build:path.write_text(json.dumps([{x:str(v) for x,v in p.items()},{i:str(v) for i,v in y.items()}],separators=(',',':'))+'\n')


if __name__=='__main__':
    import sys
    if '--find' in sys.argv:find()
    else:replay('--build' in sys.argv)
