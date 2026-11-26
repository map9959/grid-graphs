"""Bound the joint strip by pricing overlapping substrip projections independently."""
from .nine_dual import read_dual,scale,projected
from .seven_threshold import *
import subprocess

path=file.with_name('thirteen_upper_109.json')
def price(cost,offset,H,eps,sample=True):
    inp=' '.join(str(cost.get((offset,h,r,m),0)) for h in range(25) for r in range(H-2) for m in range(512))
    cmd=[f'target/price13_{H}']+([] if eps is None else [str(round(eps*scale))]+(['sample'] if sample else []))
    lines=subprocess.run(cmd,input=inp,text=True,capture_output=True,check=True).stdout.splitlines()
    v,n=map(int,lines[0].split());arcs=set()
    for line in lines[1:]:
        j,a,b,p,c=map(int,line.split());arcs.add((j,(a,b,tuple(p>>(4*i)&15 for i in range(H))),c))
    return Q(v,scale),n,arcs

def layout(labels,blocks):
    return {(o,h,r-o,m):x for o,H in blocks for (h,r,m),x in labels.items() if o<=r<o+H-2}

def joint_oracle(cost,budget,emit=False,beam=False,paths=False):
    inp=' '.join(str(cost.get((o,h,r,m),0)) for o in (0,4) for h in range(25) for r in range(7) for m in range(512))
    p=subprocess.run(['target/thirteen_price',str(budget)]+(['paths'] if paths else ['beam'] if beam else ['emit'] if emit else []),input=inp,text=True,capture_output=True)
    if p.returncode==2:return None
    p.check_returncode();head,*lines=p.stdout.splitlines();v,n=map(int,head.split());arcs=set()
    for line in lines:
        j,a,b,bits,c=map(int,line.split());s=a,b,tuple(bits>>(4*i)&15 for i in range(13));arcs.add((j,s,c))
    return Q(v,scale),n,arcs

def check():
    ns,A,b,obj,l=model(13);data=json.loads(path.read_text());blocks,yy,cc=data[:3]
    from .thirteen_local import overlaps
    for terms in overlaps(l):A.append((terms,'='));b.append(0)
    y={int(i):Q(q) for i,q in yy.items()};c={tuple(k):q for k,q in cc};labs=layout(l,blocks)
    assert all(0<=o<=13-H for o,H in blocks) and c.keys()<=labs.keys()
    assert max(projected(A,b,obj,labs,y,{k:Q(q,scale) for k,q in c.items()}).values())<=0
    ub=sum(w*b[i] for i,w in y.items())
    if len(data)==4:
        assert blocks==[[0,9],[4,9]]
        v,n,_=joint_oracle(c,data[3]);print('joint pricing lower',v,'retained arc visits',n);ub-=v
    else:
        for o,H in blocks:
            v,n,_=price(c,o,H,None);print('offset',o,'height',H,'priced legal arcs',n,'minimum',v);ub-=v
    print('exact joint thirteen-row upper',ub,'=',float(ub));return ub

def seeds(blocks):
    start,lower,_=pathspec(13);_,aa=json.loads(lower.read_text());f=defaultdict(dict)
    for j,(a,b),p,c,q in aa:f[j,(a,b,tuple(p))][c]=Q(q)
    prior={o:set() for o,H in blocks}
    while f[0,start]:
        s=start;word=[];ps=[]
        for j in range(109):
            c=next(iter(f[j,s]));ps.append((j,s,c));word.append(c);s=s[1],c,move(s[1],s[2],c)
        z=min(f[j,s][c] for j,s,c in ps)
        for j,s,c in ps:
            f[j,s][c]-=z
            if not f[j,s][c]:del f[j,s][c]
        for o,H in blocks:
            s=0,0,tuple(range(H))
            for j,c in enumerate(word):
                c=(c>>o)&((1<<H)-1);prior[o].add((j,s,c));s=s[1],c,move(s[1],s[2],c);assert s[2] is not None
    return prior

def build(blocks,extra=False,bundle=False,joint=False,wide=False,lift=False,resume=False,box=False):
    from .side28_score import solve
    ns0,A0,b0,obj,l=model(13);labs=layout(l,blocks);freq=Counter(labs.values())
    if extra:
        from .thirteen_local import overlaps
        for terms in overlaps(l):A0.append((terms,'='));b0.append(0)
    # Begin with the nine-row upper. Push coarse multipliers down along
    # the three successive bucket refinements before pricing substrips.
    first=11 if lift else blocks[0][1]
    y,old=read_dual(file.with_name(('eleven' if first==11 else 'nine')+'_upper_109.json'))
    def label(H,h,r,m):
        j=reps[H][h];pos=[tuple(fine_axis(t,H) for t in trans(r,j,107,g)) for g in range(8)]
        return ns0[{9:'p',11:'fine',12:'finer',13:'fine13'}[H],min(zip(pos,SYM[m]))]
    reps={H:{fine_axis(j,H):j for j in range(107)} for H in (9,11,12,13)}
    previous=first
    agg={tuple(cs):i for i,(cs,op) in enumerate(A0) if op=='='}
    for H in range(max(11,first+1),14):
        new={};split=H-3
        for (h,r,m),v in old.items():
            hs=[h]+[fine_axis(j,H) for j in (split,106-split) if fine_axis(j,H-1)==h]
            terms=Counter(label(H,t,r,m) for t in hs);terms[label(previous,h,r,m)]=-1
            i=agg[tuple(sorted(terms.items()))];y[i]=y.get(i,0)+Q(v,scale)
            for t in hs:new[t,r,m]=v
        old=new;previous=H
    c={(o,h,r,m):Q(old.get((h,r+o,m),0),scale) if (o==0 or r+o>=blocks[0][1]-2) else Q(0) for o,h,r,m in labs}
    mir={fine_axis(j,13):fine_axis(106-j,13) for j in range(107)}
    rows=[];norm={};unlinked={}
    for i,((terms,op),bb) in enumerate(zip(A0,b0)):
        if bb>0 and op=='=' and all(w>0 for x,w in terms):
            for x,w in terms:norm[x]=i,w
        if bb==0 and any(x[0] in 'fgh' and w>0 for x,w in terms) and len({x[0] for x,w in terms})>1:
            parent=next(x for x,w in terms if w==-1);rows.append((i,parent,terms))
            for x,w in terms:
                if w>0:unlinked[x]=i,w
    def tighten(y,c):
        rc=projected(A0,b0,obj,labs,y,c)
        for i,x,terms in rows:
            q=max(-rc[x],0)
            if q:
                y[i]=y.get(i,0)+q
                for z,w in terms:rc[z]-=w*q
        cp={k:c.get(k,0)-rc[x]/freq[x] for k,x in labs.items()}
        return {(o,h,r,m):(q+cp[o,mir[h],r,((m&73)<<2)|(m&146)|((m&292)>>2)])/2 for (o,h,r,m),q in cp.items()}
    snapshot=Path('target/thirteen_trial_'+str(first)+('_wide' if wide else '')+'.json')
    if resume:
        _,yy,cc=json.loads(snapshot.read_text());y={int(i):Q(q) for i,q in yy.items()};c={tuple(k):Q(q,scale) for k,q in cc}
        snapshot=Path('target/thirteen_diverse.json' if box else 'target/thirteen_resumed.json')
    c=tighten(y,c);prior=seeds(blocks);center=c.copy();best=None
    if joint:
        _,aa=json.loads(pathspec(13)[1].read_text())
        prior={0:{(j,(a,v,tuple(p)),c0) for j,(a,v),p,c0,q in aa}}
    # Small convex master: a candidate dual pays its core RHS minus the
    # price of a tuple of strip words. Mix candidates using all such
    # inequalities discovered by exact pricing.
    ensemble=[];wcuts=[];active=None
    def payoff(dual,words):
        rr,cc=dual
        return rr-Q(sum(z*cc.get(k,0) for k,z in words.items()),scale)
    def mixture():
        import numpy as np
        import highspy as hs
        h=hs.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
        n=len(ensemble);h.addVars(n+1,[0.]*n+[4080.],[1.]*n+[4200.]);h.changeColCost(n,1.)
        h.addRow(1,1,n,list(range(n)),[1.]*n)
        for w in wcuts:
            h.addRow(-hs.kHighsInf,0,n+1,list(range(n+1)),[float(payoff(e[0],w)) for e in ensemble]+[-1.])
        h.run();assert h.getModelStatus()==hs.HighsModelStatus.kOptimal
        ws=[Q(max(0,v)).limit_denominator(10**6) for v in h.getSolution().col_value[:n]]
        return [w/sum(ws) for w in ws]
    for it in range(150):
        y={i:Q(round(q*scale),scale) for i,q in y.items() if q}
        costs={k:round(q*scale) for k,q in c.items() if q}
        rc=projected(A0,b0,obj,labs,y,{k:Q(q,scale) for k,q in costs.items()})
        for i,_,terms in reversed(rows):
            q=max([rc[x]/w for x,w in terms if w>0 and x not in norm]+[0])
            if q>0:
                y[i]=y.get(i,0)+q
                for x,w in terms:rc[x]-=w*q
        adj=Counter()
        for x,z in rc.items():
            if z>0:
                i,w=norm[x];adj[i]=max(adj[i],z/w)
        for i,q in adj.items():y[i]=y.get(i,0)+q
        ub=sum(q*b0[i] for i,q in y.items())
        if bundle:
            ensemble.append(((ub,costs),y))
            if len(ensemble)>1:
                # Interpolate the promising newest candidate and the
                # current best even when the pricing bundle has few cuts.
                ww=mixture()
                rr=0;cc=Counter();yy=Counter()
                for w,((rhs,dd),yv) in zip(ww,ensemble):
                    if not w:continue
                    rr+=w*rhs
                    for k,z in dd.items():cc[k]+=w*z
                    for i,z in yv.items():yy[i]+=w*z
                ub=rr;costs={k:z.__floor__() for k,z in cc.items()};y=dict(yy)
        words=Counter();budget=None
        if joint:
            rhs=ub;budget=((rhs-4094)*scale).__floor__()
            result=joint_oracle(costs,budget,paths=True)
            base=sum(price(costs,o,H,None)[0] for o,H in blocks)
            if result is not None:
                dist,n,found=result;ub-=dist;prior[0].update(found)
            else:ub-=base
            if ub>=4094 and it:
                collect=joint_oracle(costs,budget,beam=True)
                if collect:prior[0].update(collect[2])
        for o,H in ([] if joint else blocks):
            # Initially lower windows may have heavily degenerate pricing.
            # Skip their corridor until the master supplies nonzero prices.
            eps=None if it==0 else (.25 if wide else 0. if bundle else .001)
            dist,n,aa=price(costs,o,H,eps);ub-=dist;prior[o].update(aa)
            if bundle:
                dag=defaultdict(list)
                for j,s,c0 in aa:dag[j,s].append(c0)
                s=0,0,tuple(range(H))
                for j in range(109):
                    c0=min(dag[j,s]);a,v,p=s;s=v,c0,move(v,p,c0)
                    if j>=2:words.update((o,fine_axis(j-2,13),r,m) for r,m in enumerate(masks(a,v,c0,H)))
        if bundle:wcuts.append(words)
        print(it,'upper',float(ub),'arcs',*[len(v) for v in prior.values()],flush=True)
        if best is None or ub<best:
            best=ub;center={k:Q(costs.get(k,0),scale) for k in labs}
            snapshot.write_text(json.dumps([blocks,{i:str(q) for i,q in y.items() if q},[[k,q] for k,q in costs.items() if q]],separators=(',',':')))
            if ub<4094:
                path.write_text(json.dumps([blocks,{i:str(q) for i,q in y.items() if q},[[k,q] for k,q in costs.items() if q]]+([budget] if joint else []),separators=(',',':'))+'\n')
                assert check()<4094;return
        A=A0.copy();b=b0.copy();ns=ns0.copy();objective=obj.copy();bounds={};links=defaultdict(list)
        for o,H in ([(0,13)] if joint else blocks):
            flow=defaultdict(list)
            for i,(j,s,c0) in enumerate(sorted(prior[o])):
                a,v,p=s;d=move(v,p,c0);assert d is not None
                x=f'z{o}_{i}';ns[o,j,s,c0]=x;flow[j,s].append((x,1))
                if j<108:flow[j+1,(v,c0,d)].append((x,-1))
                if j>=2:
                    for r,m in enumerate(masks(a,v,c0,H)):links[o,fine_axis(j-2,13),r,m].append((x,1))
            for k,cs in flow.items():A.append((cs,'='));b.append(int(k==(0,(0,0,tuple(range(H))))))
        base=len(A)
        for i,(k,x) in enumerate(labs.items()):
            terms=links[(0,k[1],k[0]+k[2],k[3]) if joint else k]+[(x,-1)];mult=30 if 8<=k[1]<=10 else 1
            for sign in (-1,1):
                art=f'u{i}_{sign}';ns['box',i,sign]=art;terms.append((art,sign))
                bounds[art]=.002*mult;objective[art]=sign*float(center[k])-.0001/mult
                if box:
                    z=art+'B';ns['wall',i,sign]=z;terms.append((z,sign));objective[z]=sign*float(center[k])-.18/mult
            A.append((terms,'='));b.append(0)
        val,raw,_=solve(A,b,objective,ns,interior=True,bounds=bounds);print('master',val,flush=True)
        y=dict(enumerate(raw[:len(A0)]));c=tighten(y,dict(zip(labs,raw[base:])))
        if it==0:
            ym=y.copy();cm=c.copy()
        else:
            a=.4 if box else .15 if wide else .45
            ym={i:(1-a)*ym.get(i,0)+a*y.get(i,0) for i in ym.keys()|y.keys()}
            cm={k:(1-a)*cm[k]+a*q for k,q in c.items()};y=ym.copy();c=cm.copy()

if __name__=='__main__':
    import sys
    if '--build' in sys.argv:build([(0,11 if '--deep' in sys.argv else 9),(4,9)],'--overlap' in sys.argv,'--bundle' in sys.argv,'--joint' in sys.argv,'--wide' in sys.argv,'--lift' in sys.argv,'--resume' in sys.argv,'--box' in sys.argv)
    else:check()
