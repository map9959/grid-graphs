"""Sparse primal/dual generation and exact path-based replay for the six-row optimum."""
from .six_joint_lp import core,layer,advance6,masks6,Q,Path,json,axis,Counter,defaultdict
from .all_pinned_sites import primal


def subset(ns,A,b,obj,labels,keep):
    ns=ns.copy();A=A.copy();b=b.copy()
    start=(0,0,tuple(range(6)));layers=[];states={start}
    for j in range(109):
        nxt=set();arcs=[]
        for s in sorted(states):
            for c in range(64):
                d=advance6(s,c)
                if d is None:continue
                keys=[(axis(j-2,107),r,m) for r,m in enumerate(masks6(*s[:2],c))] if j>=2 else []
                if any(labels[k] not in keep for k in keys):continue
                arcs.append((s,c,d,keys));nxt.add(d)
        states=nxt;layers.append(arcs)
    for j in reversed(range(109)):
        layers[j]=[a for a in layers[j] if a[2] in states];states={a[0] for a in layers[j]}
    flow=defaultdict(list);links=defaultdict(list)
    for j,arcs in enumerate(layers):
        for i,(s,c,d,keys) in enumerate(arcs):
            x=f'z{j}_{i}';ns['arc',j,s,c]=x
            flow[j,s].append((x,1))
            if j<108:flow[j+1,d].append((x,-1))
            for k in keys:links[k].append((x,1))
    for k,x in labels.items():A.append((tuple(links[k]+[(x,-1)]),'='));b.append(0)
    for k,terms in sorted(flow.items()):A.append((tuple(terms),'='));b.append(int(k==(0,start)))
    return ns,A,b,flow


def old_support():
    path=Path(__file__).parent;support=set()
    for fn in ('full_top_109','six_cover_replacement_109','six_cover_local_replacement_109','redistributed_transfer_109','redistributed_strip_109','all_pinned_joint_109'):
        d=json.loads((path/(fn+'.json')).read_text())
        if isinstance(d,list):d=d[0]
        support.update(x for x,w in d.items() if x.startswith('x') and Q(w))
    return support


def lower():
    from .side28_score import solve
    ns,A,b,obj,labels=core()
    ns,A,b,flow=subset(ns,A,b,obj,labels,old_support())
    print('restricted six-strip arcs',len(ns)-len(obj),'states',len(flow),flush=True)
    score,_,v=solve(A,b,obj,ns);print('candidate lower',score,flush=True)
    p=primal(A,b,v)
    assert min(p.values())>=0
    for (row,op),rhs in zip(A,b):
        diff=sum(w*p.get(x,0) for x,w in row)-rhs
        assert {'=':diff==0,'<=':diff<=0,'>=':diff>=0}[op]
    val=sum(w*p.get(x,0) for x,w in obj.items());print('exact lower',val,flush=True)
    save(p,ns,'six_lower_109')


def save(p,ns,stem):
    y={x:str(v) for x,v in p.items() if v and not x.startswith('z')}
    arcs=[[j,list(s[:2]),list(s[2]),c,str(p[x])] for k,x in ns.items() if k[0]=='arc' and p.get(x) for _,j,s,c in [k]]
    Path(__file__).with_name(stem+'.json').write_text(json.dumps([y,arcs],separators=(',',':'))+'\n')


def replay(stem='six_lower_109'):
    ns,A,b,obj,labels=core()
    pp,arcs=json.loads(Path(__file__).with_name(stem+'.json').read_text())
    p={x:Q(w) for x,w in pp.items()};assert min(p.values())>=0 and p.keys()<=set(ns.values())
    for (row,op),rhs in zip(A,b):
        diff=sum(w*p.get(x,0) for x,w in row)-rhs
        assert {'=':diff==0,'<=':diff<=0,'>=':diff>=0}[op]
    start=(0,0,tuple(range(6)));balance=Counter();emit=Counter()
    for j,ab,part,c,w in arcs:
        s=(*ab,tuple(part));q=Q(w);assert q>0 and 0<=j<109 and 0<=c<64
        d=advance6(s,c);assert d is not None
        balance[j,s]+=q
        if j<108:balance[j+1,d]-=q
        if j>=2:
            for r,m in enumerate(masks6(*ab,c)):emit[axis(j-2,107),r,m]+=q
    assert balance.pop((0,start))==1 and all(w==0 for w in balance.values())
    assert emit.keys()<=labels.keys() and all(emit[k]==p.get(x,0) for k,x in labels.items())
    score=sum(w*p.get(x,0) for x,w in obj.items())
    print('replayed',len(arcs),'positive six-row arcs,',len(labels),'exact patch totals; score',score)
    return score


if __name__=='__main__':
    import sys
    if '--replay' in sys.argv:replay()
    else:lower()
