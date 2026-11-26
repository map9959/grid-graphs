"""Verify a six-strip dual without storing a million arc inequalities."""
from .six_joint_lp import *
from .top6_sparse import replay
from math import lcm


def projected(A,b,obj,labels,y,cost):
    rc=Counter(obj)
    for i,q in y.items():
        cs,op=A[i]
        assert op=='=' or (q>=0 if op=='<=' else q<=0)
        for x,w in cs:rc[x]-=q*w
    for k,q in cost.items():rc[labels[k]]+=q
    return rc


def price(cost):
    scale=lcm(*(q.denominator for q in cost.values()))
    iw={k:int(q*scale) for k,q in cost.items()}
    dp={(0,0,tuple(range(6))):0};states=tuple(dp);ca={};count=0
    for j in range(109):
        arcs,ns=layer(states);h=axis(j-2,107) if j>=2 else -1;key=(id(arcs),h)
        if key not in ca:ca[key]=[(s,d,sum(iw.get((h,r,m),0) for r,m in enumerate(ms)) if h>=0 else 0) for s,c,d,ms in arcs]
        nd={}
        for s,d,z in ca[key]:
            v=dp[s]+z
            if d not in nd or v<nd[d]:nd[d]=v
        dp=nd;states=ns;count+=len(arcs)
    return Q(min(dp.values()),scale),count


def rounded(raw,den,exact=False):
    ns,A,b,obj,labels=core();base=len(A);keys=list(labels)
    conv=(lambda a:Q(float(a)).limit_denominator(den)) if exact else (lambda a:Q(round(a*den),den))
    y={i:conv(a) for i,a in enumerate(raw[:base]) if a}
    costs={k:conv(a) for k,a in zip(keys,raw[base:base+len(keys)]) if a}
    rc=projected(A,b,obj,labels,y,costs)
    # Repair positive core residuals through exact probability normalizations.
    # Several variables can share a normalizer: one maximum per row suffices.
    normal={}
    for i,((cs,op),bb) in enumerate(zip(A,b)):
        if bb>0 and op=='=' and all(w>0 for x,w in cs):
            for x,w in cs:normal[x]=(i,w)
    adj=Counter()
    for x,r in rc.items():
        if r>0:
            i,w=normal[x];adj[i]=max(adj[i],r/w)
    for i,z in adj.items():y[i]=y.get(i,0)+z
    assert max(projected(A,b,obj,labels,y,costs).values())<=0
    shortest,n=price(costs)
    val=sum(z*b[i] for i,z in y.items())-shortest
    print('exact physical upper',val,'=',float(val),'physical arcs',n,'normalizer repairs',len(adj),flush=True)
    return val,y,costs


def check(path):
    ns,A,b,obj,labels=core()
    yp,cp=json.loads(path.read_text())
    y={int(i):Q(w) for i,w in yp.items()};cost={tuple(k):Q(w) for k,w in cp}
    assert max(projected(A,b,obj,labels,y,cost).values())<=0
    dist,n=price(cost)
    upper=sum(v*b[i] for i,v in y.items())-dist
    print('exact dual replay',upper,'arcs',n)
    return upper


def save(y,cost,path):
    path.write_text(json.dumps([{i:str(v) for i,v in y.items() if v},[[k,str(v)] for k,v in cost.items() if v]],separators=(',',':'))+'\n')


def inherited():
    ns,A,b,obj,labels=core();base=len(A)
    keys=list(data(109,0,ns,{})[0])
    _,yy=json.loads(Path(__file__).with_name('full_top_109.json').read_text())
    y={int(i):Q(w) for i,w in yy.items() if int(i)<base}
    cost={k:Q(yy.get(str(base+i),0)) for i,k in enumerate(keys)}
    assert max(projected(A,b,obj,labels,y,cost).values())<=0
    dist,arcs=price(cost)
    ub=sum(w*b[i] for i,w in y.items())-dist
    print('complete six-strip dual certified upper',ub,'physical arcs',arcs)
    return ub


def recover_full():
    """Read a crossover basis solution; retain only positive columns for primal recovery."""
    import numpy as np
    from .all_pinned_sites import primal
    ns,A,b,obj,labels=core();sol=np.load('target/six_joint_sol.npz')
    pv=sol['p'];ys=sol['y'];N=len(ns);A0=len(A)
    raw={x:pv[i] for i,x in enumerate(ns.values()) if pv[i]>1e-9}
    keys=list(labels);links=defaultdict(list);flows=defaultdict(list)
    start=(0,0,tuple(range(6)));states=(start,)
    rec=[];offset=N
    for j in range(109):
        arcs,states=layer(states)
        for i in np.flatnonzero(pv[offset:offset+len(arcs)]>1e-9):
            s,c,d,ms=arcs[i];x='z'+str(offset+i);raw[x]=pv[offset+i]
            rec.append((j,s,c,x));flows[j,s].append((x,1))
            if j<108:flows[j+1,d].append((x,-1))
            if j>=2:
                for r,m in enumerate(ms):links[axis(j-2,107),r,m].append((x,1))
        offset+=len(arcs)
    assert offset==len(pv)
    sub=[(tuple((x,w) for x,w in cs if x in raw),op) for cs,op in A];rhs=list(b)
    for k in keys:
        x=labels[k];sub.append((tuple(links[k]+([(x,-1)] if x in raw else [])),'='));rhs.append(0)
    for k,terms in flows.items():sub.append((tuple(terms),'='));rhs.append(int(k==(0,start)))
    p=primal(sub,rhs,raw)
    assert min(p.values())>=0
    for (cs,op),bb in zip(sub,rhs):
        z=sum(w*p.get(x,0) for x,w in cs)-bb
        assert {'=':z==0,'>=':z>=0,'<=':z<=0}[op]
    out=[{x:str(w) for x,w in p.items() if not x.startswith('z') and w},
         [[j,list(s[:2]),list(s[2]),c,str(p[x])] for j,s,c,x in rec if p.get(x)]]
    Path(__file__).with_name('six_full_109.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    score=replay('six_full_109')
    for den,rat in ((10**6,True),(10**10,False)):
        ub,y,c=rounded(ys,den,rat)
        if ub==score:
            save(y,c,Path(__file__).with_name('six_full_dual_109.json'));return
    print('exact dual recovery still needed for equality to',score)


if __name__=='__main__':
    import sys
    if '--recover' in sys.argv:
        recover_full();sys.exit()
    l=replay();u=inherited()
    assert l<=u and int(l)==int(u)
    print('certified floor of complete six-row optimum',int(l))
