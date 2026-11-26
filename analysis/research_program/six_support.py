"""Support pricing on a joint six-row frontier, free to redistribute phase totals."""
from .top5_lift import relaxation,axis,trans,MASKS,SYM,Q,Path,json
from functools import lru_cache


@lru_cache(None)
def advance6(state,c):
    _,b,part=state
    p=list(part)+list(range(6,12))
    def root(i):
        while p[i]!=i:i=p[i]
        return i
    for u,v,on in [(i,i+6,(b|c)>>i&1) for i in range(6)]+[(i+6,i+7,(c|c>>1)>>i&1) for i in range(5)]:
        if on:
            x,y=root(u),root(v)
            if x==y:return None
            p[x]=y
    roots=[root(i) for i in range(6,12)]
    return b,c,tuple(roots.index(x) for x in roots)


@lru_cache(None)
def masks6(a,b,c):
    return tuple(sum(((z>>(r+i))&1)<<(3*i+h) for h,z in enumerate((a,b,c)) for i in range(3)) for r in range(4))


def setup(n,ns,p):
    S=n-2;labels={}
    for j in range(S):
        for r in range(4):
            pos=[tuple(axis(t,S) for t in trans(r,j,S,g)) for g in range(8)]
            for m in MASKS:
                k=axis(j,S),r,m;x=ns['p',min(zip(pos,SYM[m]))]
                assert labels.setdefault(k,x)==x
    mass={k:p[x] for k,x in labels.items() if p.get(x,0)}
    states={(0,0,tuple(range(6)))};layers=[]
    for j in range(n):
        arcs=[];nxt=set()
        for s in sorted(states):
            for c in range(64):
                ev=[(axis(j-2,S),r,m) for r,m in enumerate(masks6(*s[:2],c))] if j>=2 else []
                if any(k not in mass for k in ev):continue
                d=advance6(s,c)
                if d is not None:arcs.append((s,d,ev));nxt.add(d)
        layers.append(arcs);states=nxt
    return labels,mass,layers


def price(g,y):
    dp={(0,0,tuple(range(6))):0};hs=[]
    for arcs in g:
        nd={};pred={}
        for s,d,ev in arcs:
            if s not in dp:continue
            z=dp[s]+sum(y.get(k,0) for k in ev)
            if d not in nd or z<nd[d]:nd[d]=z;pred[d]=(s,ev)
        dp=nd;hs.append(pred)
    if not dp:return 1,[]
    d=min(dp,key=dp.get);val=dp[d];path=[]
    for pred in reversed(hs):d,ev=pred[d];path+=ev
    return val,path


def find():
    import highspy as H
    from collections import Counter
    ns,_,_=relaxation(25,9,pooled=5,period=3)
    pp,_=json.loads(Path(__file__).with_name('full_top_109.json').read_text())
    labels,mass,g=setup(109,ns,{x:Q(v) for x,v in pp.items()})
    for bulk in (False,True):
        ev=[k for k in mass if bulk or not 8<=k[0]<=10];ids={k:i for i,k in enumerate(ev)}
        h=H.Highs();h.setOptionValue('output_flag',False);h.setOptionValue('threads',1)
        h.addVars(len(ev),[0.]*len(ev),[1.]*len(ev))
        h.changeColsCost(len(ev),list(range(len(ev))),[float(mass[k]) for k in ev])
        while True:
            h.run()
            if h.getObjectiveValue()>=.999999:break
            y={k:Q(float(w)).limit_denominator(100000) for k,w in zip(ev,h.getSolution().col_value) if w>1e-9}
            val,path=price(g,y)
            if val>=1:
                score=sum(w*mass[k] for k,w in y.items())
                print('cover',score,y,flush=True);return
            terms=Counter(ids[k] for k in path if k in ids)
            if not terms:break
            h.addRow(1,H.kHighsInf,len(terms),list(terms),list(terms.values()))
    print('no cut')


if __name__=='__main__':find()
