"""Separate strip marginals by a nonnegative event cover, with shortest-path pricing."""
from .four_row_separator import *


def graph(n,i,prob):
    states={(0,0,(0,1,2,3))};layers=[]
    for j in range(n):
        arcs=[];new=set()
        for s in sorted(states):
            for c in range(16):
                ev=[(j-2,r,m) for r,m in enumerate(masks(*s[:2],c))] if j>=2 else []
                if any(m not in prob(i+r,t) for t,r,m in ev):continue
                d=advance(s,c)
                if d is not None:arcs.append((s,d,ev));new.add(d)
        layers.append(arcs);states=new
    return layers


def shortest(layers,cost):
    dp={(0,0,(0,1,2,3)):0};hist=[]
    for arcs in layers:
        nd={};pred={}
        for s,d,ev in arcs:
            if s not in dp:continue
            z=dp[s]+sum(cost.get(k,0) for k in ev)
            if d not in nd or z<nd[d]:nd[d]=z;pred[d]=s,ev
        dp=nd;hist.append(pred)
    d=min(dp,key=dp.get);v=dp[d];path=[]
    for pred in reversed(hist):
        d,ev=pred[d];path.extend(ev)
    return v,path


def find(n=28,i=6):
    import highspy as H
    p=probabilities(n);g=graph(n,i,p)
    # Favor boundary events: we want a certificate expressible for all n.
    keys=[(j,r,m) for j,r in product(range(n-2),range(2)) for m in sorted(p(i+r,j))]
    for end in (1,2,4,7,10,n):
        ev=[k for k in keys if min(k[0],n-3-k[0])<end]
        h=H.Highs();h.setOptionValue('output_flag',False);h.setOptionValue('threads',1)
        h.addVars(len(ev),[0.]*len(ev),[1.]*len(ev))
        h.changeColsCost(len(ev),list(range(len(ev))),[float(p(i+r,j)[m]) for j,r,m in ev]);ids={k:z for z,k in enumerate(ev)}
        while True:
            h.run();s=h.getObjectiveValue()
            if s>=.999999:break
            y={k:Q(float(w)).limit_denominator(10000) for k,w in zip(ev,h.getSolution().col_value) if w>1e-8}
            v,path=shortest(g,y)
            if v>=1:
                score=sum(w*p(i+r,j)[m] for (j,r,m),w in y.items())
                print('n',n,'row',i,'cover score',score,'weights',y,flush=True)
                return y
            active=[ids[k] for k in path if k in ids]
            if not active:break
            h.addRow(1,H.kHighsInf,len(active),active,[1.]*len(active))
    print('no supported separator',n,i)


if __name__=='__main__':
    import sys
    find(int(sys.argv[1]) if len(sys.argv)>1 else 28)
