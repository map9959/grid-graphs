"""Fast exact face test: can a four-strip-optimal core extend to five rows?"""
from .full_top_transfer import *
from .patch_square import relaxation


def labels5(ns):
    out={}
    for j in range(107):
        c=axis(j,107)
        if (c,2,MASKS[0]) in out:continue
        for r in range(3):
            pos=[tuple(axis(v,107) for v in trans(r,j,107,g)) for g in range(8)]
            for m in MASKS:out[c,r,m]=ns['p',min(zip(pos,SYM[m]))]
    return out


def test():
    from .side28_score import solve
    ns,_,_=relaxation(25,9,pooled=5,period=3)
    labels=labels5(ns)
    pp,_=json.loads(Path(__file__).with_name('full_top_109.json').read_text())
    p={x:Q(w) for x,w in pp.items() if not x.startswith('z')}
    start=(0,0,tuple(range(5)));states={start}
    balance=defaultdict(list);links=defaultdict(list);names={}
    for j in range(109):
        nxt=set()
        for s in sorted(states):
            for c in range(32):
                d=advance5(s,c)
                if d is None:continue
                keys=[(axis(j-2,107),r,m) for r,m in enumerate(masks5(*s[:2],c))] if j>=2 else []
                if any(labels[k] not in p for k in keys):continue
                x=f'z{len(names)}';names[j,s,c]=x;balance[j,s].append((x,1))
                if j<108:balance[j+1,d].append((x,-1))
                for k in keys:links[k].append((x,1))
                nxt.add(d)
        states=nxt
    A=[];rhs=[]
    for k,terms in balance.items():A.append((tuple(terms),'='));rhs.append(int(k==(0,start)))
    for k,x in labels.items():
        if x in p:A.append((tuple(links[k]),'='));rhs.append(p[x])
    print('four-row primal support, admissible 5-row arcs',len(names),flush=True)
    _,_,raw=solve(A,rhs,{},names)
    v=primal(A,rhs,raw)
    assert min(v.values())>=0 and all(sum(w*v.get(x,0) for x,w in cs)==b for (cs,_),b in zip(A,rhs))
    print('exact lift on old core')
    Path(__file__).with_name('top5_lift_109.json').write_text(json.dumps([[j,list(s[:2]),list(s[2]),c,str(v[x])] for (j,s,c),x in names.items() if v.get(x)],separators=(',',':'))+'\n')


def replay():
    ns,A,rhs,obj,base=model(5)
    pp,yy=json.loads(Path(__file__).with_name('full_top_109.json').read_text())
    p={x:Q(w) for x,w in pp.items() if not x.startswith('z')}
    lift={(j,(*ab,tuple(part)),c):Q(w) for j,ab,part,c,w in json.loads(Path(__file__).with_name('top5_lift_109.json').read_text())}
    # The two old patch rows have the identical link order. Price every
    # physical five-row path using these duals; set third-row prices to zero.
    y={int(i):Q(w) for i,w in yy.items() if int(i)<base+3800}
    keys=list(data(109,0,ns,{})[0])
    prices={k:y.get(base+i,0) for i,k in enumerate(keys)}
    zero=(0,0,tuple(range(5)));states={zero};layers=[];count=0
    from math import lcm
    scale=lcm(*(Q(w).denominator for w in prices.values()))
    iw={k:int(w*scale) for k,w in prices.items()}
    for j in range(109):
        arcs=[];nxt=set()
        for s in sorted(states):
            for c in range(32):
                d=advance5(s,c)
                if d is None:continue
                cost=sum(iw.get((axis(j-2,107),r,m),0) for r,m in enumerate(masks5(*s[:2],c)[:2])) if j>=2 else 0
                arcs.append((s,d,cost));nxt.add(d)
                if (j,s,c) in lift:p[f'z{count}']=lift.pop((j,s,c))
                count+=1
        layers.append(arcs);states=nxt
    assert not lift
    pots={};dist=Counter()
    for j in reversed(range(109)):
        best={}
        for s,d,cost in layers[j]:
            v=dist[d]-cost
            if s not in best or v>best[s]:best[s]=v
        pots.update({(j,s):v for s,v in best.items()});dist=best
    for i,k in enumerate(sorted(pots),base+5700):
        if pots[k]:y[i]=Q(pots[k],scale)
    assert len(A)==base+5700+len(pots)
    assert p.keys()<=set(ns.values()) and min(p.values())>=0
    for (cs,op),b in zip(A,rhs):
        z=sum(w*p.get(x,0) for x,w in cs)-b
        assert {'=':z==0,'<=':z<=0,'>=':z>=0}[op]
    score=sum(w*p.get(x,0) for x,w in obj.items())
    assert verify(A,obj,y)<=0
    bound=sum(w*rhs[i] for i,w in y.items())
    assert score==bound==Q(12293,3)
    print('five-row joint transfer verified primal',score,'dual',bound,'integer upper',int(bound))


if __name__=='__main__':
    import sys
    if '--build' in sys.argv:test()
    else:replay()
