"""Warm-started path master on symmetrized physical strip words (discovery only)."""
from .fourteen_bound import *

def run():
    import highspy as hs
    import numpy as np
    import random
    ns,A,b,obj,l,*_=core15();bl=[(0,9),(6,9)];labs=layout(l,bl);start=pathspec(15)[0]
    mir={fine_axis(j,15):fine_axis(106-j,15) for j in range(107)}
    flip=lambda k:(mir[k[0]],k[1],((k[2]&73)<<2)|(k[2]&146)|((k[2]&292)>>2))
    reps={k:min(k,flip(k)) for k in l};rows=sorted(set(reps.values()))
    rowid={k:i for i,k in enumerate(rows)};n0=len(A);norm={};agg=[]
    xs=list(ns.values());ix={x:i for i,x in enumerate(xs)}
    h=hs.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
    h.setOptionValue('solver','ipm');h.setOptionValue('run_crossover','off')
    h.addVars(len(xs),np.zeros(len(xs)),np.full(len(xs),hs.kHighsInf));h.setMaximize()
    h.changeColsCost(len(xs),np.arange(len(xs)),[obj.get(x,0) for x in xs])
    for i,((terms,op),bb) in enumerate(zip(A,b)):
        h.addRow(float(bb) if op!='<=' else -hs.kHighsInf,float(bb) if op!='>=' else hs.kHighsInf,len(terms),[ix[x] for x,w in terms],[float(w) for x,w in terms])
        if bb>0 and op=='=' and all(w>0 for x,w in terms):
            for x,w in terms:norm[x]=i,w
        if bb==0 and len({x[0] for x,w in terms})>1 and any(x[0] in 'fghij' and w>0 for x,w in terms):agg.append((i,terms))
    yy,cc,bu=json.loads(Path('target/fifteen_mixqp.json').read_text());Y={int(i):Q(q) for i,q in yy.items()};C={tuple(k):v for k,v in cc}
    table=Counter()
    for (o,p,r,m),q in C.items():table[reps[p,o+r,m]]+=q/scale
    box=h.getNumCol();mult=Counter(fine_axis(j,15) for j in range(107))
    prices=np.array([table[k] for k in rows]);wbase=np.array([1/mult[k[0]] for k in rows])
    cap=[];extra=[];signs=[];cen=[]
    for j,k in enumerate(rows):
        h.addRow(0,0,1,[ix[l[k]]],[-1.])
        for rad,lim in ((.0001,.002),(.08,.018),(.25,hs.kHighsInf)):
            for sign in (-1,1):
                cost=sign*prices[j]-rad*wbase[j]
                h.addCol(cost,0,min(hs.kHighsInf,lim/wbase[j]),1,[n0+j],[sign])
                extra.append(rad*wbase[j]);signs.append(sign);cen.append(j)
    nrm=h.getNumRow();h.addRow(1,1,0,[],[]);wordset=set()
    def add(w):
        w=min(tuple(w),tuple(reversed(w)))
        if w in wordset:return
        wordset.add(w);ct=Counter()
        for j in range(107):
            ph=fine_axis(j,15);ms=masks(*w[j:j+3],15)
            for r,m in enumerate(ms):ct[reps[ph,r,m]]+=1
        ids=[n0+rowid[k] for k in ct]+[nrm];vals=[v/(1 if k==flip(k) else 2) for k,v in ct.items()]+[1.]
        h.addCol(0,0,hs.kHighsInf,len(ids),ids,vals)
    _,aa=json.loads(pathspec(15)[1].read_text());f=defaultdict(dict)
    for j,(a,v),p,c,q in aa:f[j,(a,v,tuple(p))][c]=Q(q)
    while f[0,start]:
        s=start;w=[];ps=[]
        for j in range(109):
            c=next(iter(f[j,s]));ps.append((j,s,c));w.append(c);s=s[1],c,move(s[1],s[2],c)
        z=min(f[j,s][c] for j,s,c in ps)
        for j,s,c in ps:
            f[j,s][c]-=z
            if not f[j,s][c]:del f[j,s][c]
        add(w)
    def addarcs(aa,cost):
        layers=defaultdict(list)
        for j,s,c in aa:layers[j].append((s,c))
        dp={start:0};hist=[]
        for j in range(109):
            pr={};nd={};ph=fine_axis(j-2,15)
            for s,c in layers[j]:
                if s not in dp:continue
                a,v,p=s;d=v,c,move(v,p,c);z=dp[s];ms=masks(a,v,c,15)
                if j>=2:z+=sum(cost.get((o,ph,r,m),0) for o,_ in bl for r,m in enumerate(ms[o:o+7]))
                if d not in nd or z<nd[d]:nd[d]=z;pr[d]=s,c
            dp=nd;hist.append(pr)
        for d in sorted(dp,key=dp.get)[:128]:
            w=[]
            for pr in reversed(hist):d,c=pr[d];w.append(c)
            add(w[::-1])
    for tag in ('mixqp','aspire','main'):
        _,cc,bu=json.loads(Path('target/fifteen_'+tag+'.json').read_text())[:3];co={tuple(k):q for k,q in cc}
        res=oracle(co,bu,'witness',15)
        if res:addarcs(res[2],co)
    best=None;available=Counter(reps[p,o+r,m] for o,p,r,m in labs)
    for it in range(160):
        h.run();assert h.getModelStatus()==hs.HighsModelStatus.kOptimal
        raw=h.getSolution().row_dual;val=h.getObjectiveValue()
        y={i:Q(round(q*scale),scale) for i,q in enumerate(raw[:n0]) if q}
        costs={}
        for k in labs:
            o,p,r,m=k;g=reps[p,o+r,m]
            costs[k]=C.get(k,0)+round(scale*(raw[n0+rowid[g]]-prices[rowid[g]])/available[g])
        # Dampen jump from the latest globally feasible center.
        a=Q(1,3) if it%3!=2 else Q(2,3)
        y={i:a*y.get(i,0)+(1-a)*Y.get(i,0) for i in y.keys()|Y.keys()}
        costs={k:(a*q+(1-a)*C.get(k,0)).__floor__() for k,q in costs.items()}
        rc=projected(A,b,obj,labs,y,{k:Q(q,scale) for k,q in costs.items()})
        for i,cs in reversed(agg):
            z=max([rc[x]/w for x,w in cs if w>0 and x not in norm]+[0])
            if z>0:
                y[i]=y.get(i,0)+z
                for x,w in cs:rc[x]-=w*z
        adj=Counter()
        for x,v in rc.items():
            if v>0:
                i,w=norm[x];adj[i]=max(adj[i],v/w)
        for i,q in adj.items():y[i]=y.get(i,0)+q
        rhs=sum(q*b[i] for i,q in y.items());bu=((rhs-4092)*scale).__floor__()
        d,n,aa=oracle(costs,bu,'paths',15);ub=rhs-d
        print(it,'words',len(wordset),'master',val,'upper',float(ub),flush=True)
        if best is None or ub<best:
            best=ub;data=json.dumps([{i:str(q) for i,q in y.items() if q},[[k,q] for k,q in costs.items() if q],bu],separators=(',',':'))+'\n'
            Path('target/fifteen_master.json').write_text(data)
            if ub<4092:file.with_name('fifteen_upper_109.json').write_text(data);assert check(15)<4092;return
            Y=y;C=costs;table=Counter()
            for (o,p,r,m),q in C.items():table[reps[p,o+r,m]]+=q/scale
            prices=np.array([table[k] for k in rows]);nv=len(extra)
            h.changeColsCost(nv,np.arange(box,box+nv),prices[cen]*signs-extra)
        if aa:addarcs(aa,costs)
        res=oracle(costs,bu,'witness',15)
        if res:addarcs(res[2],costs)

if __name__=='__main__':run()
