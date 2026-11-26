"""Exact joined fourteen-row pricing, with discovery on restricted flows."""
from .thirteen_bound import layout,scale,projected
from .seven_threshold import *
from .thirteen_local import overlaps
import subprocess

blocks=[(0,9),(5,9)]
path=file.with_name('fourteen_upper_109.json')

def oracle(c,budget,mode=None,height=14):
    inp=' '.join(str(c.get((o,h,r,m),0)) for o in (0,height-9) for h in range(2*height-1) for r in range(7) for m in range(512))
    proc=subprocess.run(['target/'+('fifteen' if height==15 else 'fourteen')+'_price',str(budget)]+([mode] if mode else []),input=inp,text=True,capture_output=True)
    if proc.returncode==2 and mode=='beam':return None
    proc.check_returncode()
    head,*lines=proc.stdout.splitlines();v,n=map(int,head.split());arcs=set()
    for line in lines:
        j,a,b,p,c0=map(int,line.split());arcs.add((j,(a,b,tuple(p>>(4*i)&15 for i in range(height))),c0))
    return Q(v,scale),n,arcs

def core14(extra=False):
    ns,A,b,obj,l=model(14)
    _,A13,_,_,l13=model(13);base=len(A)
    for t in overlaps(l13):A.append((t,'='));b.append(0)
    if extra:
        from .thirteen_bound import joint_oracle
        for t in overlaps(l,14):A.append((t,'='));b.append(0)
        blocks13,_,cc,budget=json.loads(file.with_name('thirteen_upper_109.json').read_text())
        cost={tuple(k):q for k,q in cc};v,_,_=joint_oracle(cost,budget);row=Counter()
        for k,x in layout(l13,blocks13).items():row[x]+=Q(cost.get(k,0),scale)
        A.append(([(x,q) for x,q in row.items() if q],'>='));b.append(v)
    return ns,A,b,obj,l,l13,len(A13),base

def core15(extra=False):
    ns,A,b,obj,l=model(15);_,Ac,bc,_,lc,_,_,base=core14()
    newbase=len(A);A.extend(Ac[base:]);b.extend(bc[base:])
    if extra:
        for t in overlaps(l,15):A.append((t,'='));b.append(0)
        # Every 15-row word contains these 14-row windows in both
        # vertical orientations. Transfer the saved exact price bound.
        _,cc,budget=json.loads(path.read_text());cost={tuple(k):q for k,q in cc}
        dist,_,_=oracle(cost,budget,height=14);prices=Counter()
        for (o,h,r,m),q in cost.items():prices[h,o+r,m]+=q
        oldphase={fine_axis(j,15):fine_axis(j,14) for j in range(107)}
        for offset in (0,1):
            for flip in (False,True):
                row=Counter()
                for (h,r,m),x in l.items():
                    rel=r-offset
                    if 0<=rel<12:
                        z=prices[oldphase[h],11-rel if flip else rel,((m&7)<<6)|(m&56)|((m&448)>>6) if flip else m]
                        if z:row[x]+=Q(z,scale)
                A.append((list(row.items()),'>='));b.append(dist)
    return ns,A,b,obj,l,lc,base,newbase

def check(height=14,mode=None):
    pth=path if height==14 else file.with_name('fifteen_upper_109.json')
    data=json.loads(pth.read_text());yy,cc,budget=data[:3]
    _,A,b,obj,l,*_=(core14 if height==14 else core15)(len(data)>3)
    y={int(i):Q(q) for i,q in yy.items()};c={tuple(k):q for k,q in cc};labs=layout(l,[(0,9),(height-9,9)])
    assert c.keys()<=labs.keys() and all(type(v)==int for v in c.values()) and type(budget)==int
    assert all(0<=i<len(A) for i in y)
    assert max(projected(A,b,obj,labs,y,{k:Q(v,scale) for k,v in c.items()}).values())<=0
    if height==15 and mode is None:mode='three'
    d,n,_=oracle(c,budget,mode,height=height);ub=sum(q*b[i] for i,q in y.items())-d
    print('height',height,'exact upper',ub,'=',float(ub),'retained arc visits',n);return ub

def reflect_paths(arcs,height):
    """Complete words read from right to left are also legal forest words."""
    import random
    g=defaultdict(list);rng=random.Random(15109);start=0,0,tuple(range(height))
    for j,s,c in arcs:g[j,s].append(c)
    if not g[0,start]:return set()
    result=set()
    for _ in range(128):
        s=start;w=[]
        for j in range(109):
            cs=g[j,s]
            if not cs:break
            c=rng.choice(cs);w.append(c);s=s[1],c,move(s[1],s[2],c)
        if len(w)!=109:continue
        s=start
        for j,c in enumerate(reversed(w)):
            result.add((j,s,c));q=move(s[1],s[2],c);assert q is not None;s=s[1],c,q
    return result

def discover():
    from .side28_score import solve
    import sys
    residual='--residual' in sys.argv
    extra='--alt' in sys.argv or residual;height=15 if '--fifteen' in sys.argv else 14
    stem='fifteen' if height==15 else 'fourteen';prefix='target/'+stem+'_';target=4107-height
    ns0,A0,b0,obj,l,l13,oldbase,newbase=(core15 if height==15 else core14)(extra);labs=layout(l,[(0,9),(height-9,9)])
    if height==15:yy,cc,_=json.loads(path.read_text())
    else:_,yy,cc,_=json.loads(file.with_name('thirteen_upper_109.json').read_text())
    y={(j if j<oldbase else newbase+j-oldbase):Q(q) for i,q in yy.items() for j in [int(i)]}
    agg={tuple(t):i for i,(t,op) in enumerate(A0) if op=='='}
    c=Counter()
    for (o,h,r,m),v in cc:
        if not v:continue
        rr=o+r;hs=[h]+[fine_axis(j,height) for j in (height-3,109-height) if fine_axis(j,height-1)==h]
        terms=Counter(l[z,rr,m] for z in hs);terms[l13[h,rr,m]]=-1;i=agg[tuple(sorted(terms.items()))];y[i]=y.get(i,0)+Q(v,scale)
        off=0 if o==0 or rr<height-9 else height-9
        for z in hs:c[off,z,rr-off,m]+=Q(v,scale)
    if residual:
        assert height==15
        alpha=Q(3,4)
        y[len(A0)-4]=-alpha
        c={k:q*(1-alpha) for k,q in c.items()}
    c={k:c.get(k,0) for k in labs};freq=Counter(labs.values())
    rows=[];norm={}
    for i,((t,op),bb) in enumerate(zip(A0,b0)):
        if bb==0 and any(x[0] in 'fghij' and w>0 for x,w in t) and len({x[0] for x,w in t})>1:
            rows.append((i,next(x for x,w in t if w==-1),t))
        if bb>0 and op=='=' and all(w>0 for x,w in t):
            for x,w in t:norm[x]=i,w
    mir={fine_axis(j,height):fine_axis(106-j,height) for j in range(107)}
    def tighten(y,c):
        rc=projected(A0,b0,obj,labs,y,c)
        for i,x,t in rows:
            q=max(-rc[x],0)
            if q:
                y[i]=y.get(i,0)+q
                for z,w in t:rc[z]-=w*q
        cp={k:c.get(k,0)-rc[x]/freq[x] for k,x in labs.items()}
        return {(o,h,r,m):(q+cp[o,mir[h],r,((m&73)<<2)|(m&146)|((m&292)>>2)])/2 for (o,h,r,m),q in cp.items()}
    c=tighten(y,c);center=c.copy();best=None;start,fn,_=pathspec(height)
    _,aa=json.loads(fn.read_text());prior={(j,(a,b,tuple(p)),c0) for j,(a,b),p,c0,q in aa}
    trust='--trust' in sys.argv
    elastic='--elastic' in sys.argv
    reflect='--reflect' in sys.argv or elastic
    if reflect:prior.update(reflect_paths(prior,height))
    snap=Path(prefix+('residual' if residual else 'alt' if extra else 'box' if '--box' in sys.argv else 'main')+'.json')
    aspire='--aspire' in sys.argv
    prox='--prox' in sys.argv
    if '--restart' in sys.argv or prox or reflect or aspire or trust:
        yy,cc,_=json.loads(Path(prefix+('aspire.json' if trust else 'balanced.json' if elastic or aspire else 'main.json' if prox else 'box.json')).read_text())[:3];y={int(i):Q(q) for i,q in yy.items()}
        c=tighten(y,{tuple(k):Q(q,scale) for k,q in cc});center=c.copy();snap=Path(prefix+('trust.json' if trust else 'aspire.json' if aspire else 'elastic.json' if elastic else 'reflect.json' if reflect else 'prox.json' if prox else 'restart.json'))
    if trust:
        for tag in ('main','balanced','aspire','elastic'):
            _,cc,bu,*_=json.loads(Path(prefix+tag+'.json').read_text());res=oracle({tuple(k):q for k,q in cc},bu,'beam',height)
            if res:prior.update(res[2]);prior.update(reflect_paths(res[2],height))
    if prox:
        for tag in ('box','alt','restart','main'):
            if not Path(prefix+tag+'.json').exists():continue
            _,cc,bu,*_=json.loads(Path(prefix+tag+'.json').read_text())
            more=oracle({tuple(k):v for k,v in cc},bu,'beam',height)
            if more:prior.update(more[2])
    for it in range(120):
        y={i:Q(round(q*scale),scale) for i,q in y.items() if q}
        costs={k:round(q*scale) for k,q in c.items() if q}
        rc=projected(A0,b0,obj,labs,y,{k:Q(v,scale) for k,v in costs.items()})
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
        rhs=sum(q*b0[i] for i,q in y.items());budget=((rhs-target)*scale).__floor__()
        d,n,arcs=oracle(costs,budget,'paths',height);ub=rhs-d;prior.update(arcs)
        if reflect:prior.update(reflect_paths(arcs,height))
        if not arcs and ub>target and ('--restart' in sys.argv or elastic or trust):
            d2,_,arcs=oracle(costs,((rhs-ub+Q(1,4))*scale).__floor__(),'paths',height)
            prior.update(arcs);ub=min(ub,rhs-d2)
        print(it,'upper',float(ub),'paths arcs',len(arcs),flush=True)
        if best is None or ub<best:
            best=ub;center={k:Q(costs.get(k,0),scale) for k in labs}
            data=json.dumps([{i:str(q) for i,q in y.items() if q},[[k,q] for k,q in costs.items() if q],budget]+([1] if extra else []),separators=(',',':'))+'\n'
            snap.write_text(data)
            if rhs-d<target:file.with_name(stem+'_upper_109.json').write_text(data);assert check(height)<target;return
            anchor=y.copy()
        if it and len(arcs)<1000:
            more=oracle(costs,budget,'beam',height)
            if more:
                prior.update(more[2])
                if reflect:prior.update(reflect_paths(more[2],height))
        A=A0.copy();b=b0.copy();ns=ns0.copy();bounds={};objective=obj.copy();links=defaultdict(list);flow=defaultdict(list)
        for i,(j,s,c0) in enumerate(sorted(prior)):
            a,v,p=s;q=move(v,p,c0);assert q is not None
            x=f'z{i}';ns['arc',j,s,c0]=x;flow[j,s].append((x,1))
            if j<108:flow[j+1,(v,c0,q)].append((x,-1))
            if j>=2:
                for r,m in enumerate(masks(a,v,c0,height)):links[fine_axis(j-2,height),r,m].append((x,1))
        for k,cs in flow.items():A.append((cs,'='));b.append(int(k==(0,start)))
        base=len(A)
        for i,(k,x) in enumerate(labs.items()):
            o,h,r,m=k;terms=links[h,o+r,m]+[(x,-1)];mult=30 if 8<=h<=10 else 1
            for sign in (-1,1):
                art=f'u{i}_{sign}';ns['box',i,sign]=art;terms.append((art,sign))
                bounds[art]=.002*mult;objective[art]=sign*float(center[k])-.0001/mult
                if '--box' in sys.argv:
                    z=art+'B';ns['wall',i,sign]=z;terms.append((z,sign));objective[z]=sign*float(center[k])-.12/mult
                if trust:
                    # Trust region with little penalty near its center.
                    z=art+'T';ns['tr',i,sign]=z;terms.append((z,sign))
                    objective[z]=sign*float(center[k])-.012/mult
                if prox or elastic:
                    bounds[art]=(.001 if elastic else .006)*mult
                    for tag,dist,mass in ([('A',.012,.01),('B',.07,None)] if elastic else [('A',.015,.025),('B',.05,None)]):
                        z=art+tag;ns[tag,i,sign]=z;terms.append((z,sign));objective[z]=sign*float(center[k])-dist/mult
                        if mass:bounds[z]=mass*mult
            A.append((terms,'='));b.append(0)
        if aspire:
            ns['mass',0]='lambda';objective['lambda']=-(target-.08)
            for i,bb in enumerate(b):
                if bb:
                    terms,op=A[i];A[i]=(list(terms)+[('lambda',-bb)],op);b[i]=0
        val,raw,_=solve(A,b,objective,ns,interior=True,bounds=bounds);print('master',val,'arcs',len(prior),flush=True)
        y=dict(enumerate(raw[:len(A0)]));c=tighten(y,dict(zip(labs,raw[base:])))
        if not it and (prox or elastic or aspire or trust):
            ym={i:float(q) for i,q in anchor.items()};cm={k:float(q) for k,q in center.items()}
        if not it and not (prox or elastic or aspire or trust):ym=y.copy();cm=c.copy()
        else:
            a=.5 if aspire else .32 if prox else .25;ym={i:(1-a)*ym.get(i,0)+a*y.get(i,0) for i in ym.keys()|y.keys()}
            cm={k:(1-a)*cm[k]+a*q for k,q in c.items()};y=ym.copy();c=cm.copy()

if __name__=='__main__':
    import sys
    if '--build' in sys.argv:discover()
    else:check(15 if '--fifteen' in sys.argv else 14)
