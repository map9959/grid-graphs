"""Exact six-row separator tested against the joint five-row optimum at 109."""
from .six_support import setup,price,masks6
from .full_top_transfer import *


def run(build,local=False):
    ns,A,b,obj,base=model(4)
    pp,yy=json.loads(Path(__file__).with_name('full_top_109.json').read_text())
    old={x:Q(w) for x,w in pp.items() if not x.startswith('z')}
    labels,mass,g=setup(109,ns,old);event=(11,3,7)
    val,_=price(g,{event:1})
    assert g[-1] and val==1 and mass[event]==Q(1,2)
    # Localize the contradiction. Even ignoring cycles, these five
    # physical columns cannot avoid the event within the saved support.
    states={(0,0)}
    for j in range(97,102):
        states={(b,c) for a,b in states for c in range(64) if j<99 or all(
            k in mass and k!=event for k in
            [(axis(j-2,107),r,m) for r,m in enumerate(masks6(a,b,c))])}
    assert not states
    types={axis(j,107) for j in (97,98,99)}
    cs=Counter(x for k,x in labels.items() if (not local or k[0] in types) and (k not in mass or k==event))
    print('width 109: minimum event count on supported forest paths',val,'saved cover LHS',mass[event],flush=True)
    # Work directly with core variables + the five-row arcs of the
    # saved lift, but reoptimize their masses as well as the core.
    A=A[:base]+[(tuple(cs.items()),'>=')];b=b[:base]+[1]
    names={k:x for k,x in ns.items() if not x.startswith('z')}
    flow=defaultdict(list);links=defaultdict(list)
    labs={k:x for k,x in labels.items() if k[1]<3}
    arr=json.loads(Path(__file__).with_name('top5_lift_109.json').read_text())
    for j,ab,part,c,w in arr:
        s=(*ab,tuple(part));d=advance5(s,c);assert d is not None
        x=f'a{len(names)}';names[j,s,c]=x
        flow[j,s].append((x,1))
        if j<108:flow[j+1,d].append((x,-1))
        if j>=2:
            for r,m in enumerate(masks5(*ab,c)):links[axis(j-2,107),r,m].append((x,1))
    for k,x in labs.items():
        A.append((tuple(links[k]+[(x,-1)]),'='));b.append(0)
    for k,terms in sorted(flow.items()):
        A.append((tuple(terms),'='));b.append(int(k==(0,(0,0,tuple(range(5))))))
    path=Path(__file__).with_name('six_cover_'+('local_' if local else '')+'replacement_109.json')
    if build:
        from .side28_score import solve
        opt,_,v=solve(A,b,obj,names);print('restricted-support candidate',opt,flush=True)
        p=primal(A,b,v)
    else:p={x:Q(w) for x,w in json.loads(path.read_text()).items()}
    assert p.keys()<=set(names.values()) and min(p.values())>=0
    for (terms,op),bb in zip(A,b):
        z=sum(w*p.get(x,0) for x,w in terms)-bb
        assert {'=':z==0,'<=':z<=0,'>=':z>=0}[op]
    score=sum(w*p.get(x,0) for x,w in obj.items())
    print('verified five-row primal with new cut',score,'cover value',sum(w*p.get(x,0) for x,w in cs.items()))
    assert score==(Q(233549,57) if local else Q(12293,3))
    if build:path.write_text(json.dumps({x:str(w) for x,w in p.items() if w},separators=(',',':'))+'\n')


if __name__=='__main__':
    import sys
    run('--build' in sys.argv,'--local' in sys.argv)
