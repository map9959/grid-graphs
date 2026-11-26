"""Discover a side-109 dual by screened flows, then price all nine-row paths."""
import subprocess
from .seven_threshold import *
from .six_joint_replay import projected

scale=10**8
dualfile=file.with_name('nine_upper_109.json')

def oracle(cost,epsilon=None,H=9):
    inp=' '.join(str(cost.get((h,r,m),0)) for h in range(21 if H==11 else 19) for r in range(H-2) for m in range(512))
    args=['target/eleven_price' if H==11 else 'target/nine_price']+([] if epsilon is None else [str(round(scale*epsilon))])
    result=subprocess.run(args,input=inp,text=True,capture_output=True,check=True)
    head,*rows=result.stdout.splitlines()
    best,count=map(int,head.split())
    arcs=[]
    for line in rows:
        j,a,b,p,c=map(int,line.split());part=tuple((p>>(4*i))&15 for i in range(H));arcs.append((j,(a,b,part),c))
    return Q(best,scale),count,arcs

def read_dual(path):
    yy,cc=json.loads(path.read_text())
    return {int(i):Q(w) for i,w in yy.items()},{tuple(k):q for k,q in cc}

def corridor_lower(eps):
    from .side28_score import solve
    from .all_pinned_sites import primal
    H=11;ns,A,b,obj,labels=model(H);start,lower,_=pathspec(H)
    _,cost=read_dual(file.with_name('eleven_upper_109.json'))
    _,_,arcs=oracle(cost,eps,H)
    _,old=json.loads(lower.read_text())
    prior=set(arcs)|{(j,(a,v,tuple(p)),c) for j,(a,v),p,c,_ in old}
    print('candidate arc set',len(prior),flush=True)
    flow=defaultdict(list);links=defaultdict(list)
    for i,(j,s,c) in enumerate(sorted(prior)):
        a,v,p=s;d=move(v,p,c);assert d is not None
        x=f'z{i}';ns['arc',j,s,c]=x;flow[j,s].append((x,1))
        if j<108:flow[j+1,(v,c,d)].append((x,-1))
        if j>=2:
            for r,m in enumerate(masks(a,v,c,H)):links[fine_axis(j-2,H),r,m].append((x,1))
    for k,x in labels.items():A.append((links[k]+[(x,-1)],'='));b.append(0)
    for k,cs in flow.items():A.append((cs,'='));b.append(int(k==(0,start)))
    val,_,v=solve(A,b,obj,ns,interior=True);print('corridor lower',val,flush=True)
    if val>=4095-1e-4:
        sub={k:x for k,x in ns.items() if v[x]>1e-8};support=set(sub.values())
        thin=[([(x,w) for x,w in cs if x in support],op) for cs,op in A]
        _,_,v=solve(thin,b,obj,sub);save(primal(thin,b,v),ns,lower.stem);assert replay(H)>=4095

def check(H=9):
    ns,A,b,obj,labels=model(H);y,cost=read_dual(dualfile if H==9 else file.with_name('eleven_upper_109.json'))
    assert cost.keys()<=labels.keys()
    assert max(projected(A,b,obj,labels,y,{k:Q(q,scale) for k,q in cost.items()}).values())<=0
    best,n,_=oracle(cost,H=H);ub=sum(q*b[i] for i,q in y.items())-best
    print('height',H,'exact upper',ub,'=',float(ub),'legal arcs',n)
    return ub

def discover(H=9,compact=False,lean=False,phase=False,blend=False):
    from .side28_score import solve
    from .all_pinned_sites import primal
    ns0,A0,b0,obj,labels=model(H);start,lower,_=pathspec(H)
    path=dualfile if H==9 else file.with_name('eleven_upper_109.json')
    if lean or phase:
        trial=Path('target/eleven_blend_dual.json' if blend else 'target/eleven_phase_dual.json' if phase else 'target/eleven_lean_dual.json')
        if blend and not trial.exists():trial.write_bytes(Path('target/eleven_lean_dual.json').read_bytes())
        if not trial.exists():trial.write_bytes(path.read_bytes())
        path=trial
    target=4096 if H==9 else 4095
    y,cost=read_dual(path if path.exists() else (file.with_name('seven_upper_109.json') if H==9 else dualfile))
    if H==11 and not path.exists():
        # Move each inherited link multiplier to the fine->coarse
        # aggregation equation, then copy its price to each split link.
        agg={tuple(terms):i for i,(terms,op) in enumerate(A0) if terms and any(x.startswith('f') for x,w in terms) and any(w<0 for x,w in terms)}
        coarse=model(9)[-1];new={}
        for (h,r,m),q in cost.items():
            hs=[h]+[fine_axis(j,H) for j in (8,98) if axis(j,107)==h]
            parts=Counter(labels[v,r,m] for v in hs);parts[coarse[h,r,m]]=-1
            i=agg[tuple(sorted(parts.items()))];y[i]=y.get(i,0)+Q(q,scale)
            for v in hs:new[v,r,m]=q
        cost=new
    freq=Counter(labels.values());mirror={fine_axis(j,H):fine_axis(106-j,H) for j in range(107)}
    def tighten(y,c):
        rc=projected(A0,b0,obj,labels,y,c)
        if H==11:
            for i,((terms,_),bb) in enumerate(zip(A0,b0)):
                if bb or not any(x.startswith('f') for x,w in terms):continue
                parent=next((x for x,w in terms if w==-1),None)
                if not parent:continue
                room=max(-rc[parent],0)
                if room:
                    y[i]=y.get(i,0)+room
                    for x,w in terms:rc[x]-=room*w
        cp={k:c.get(k,0)-rc[x]/freq[x] for k,x in labels.items()}
        refl=lambda m:((m&73)<<2)|(m&146)|((m&292)>>2)
        return {k:(q+cp[mirror[k[0]],k[1],refl(k[2])])/2 for k,q in cp.items()}
    center=tighten(y,{k:Q(q,scale) for k,q in cost.items()})
    norm={}
    for i,((cs,op),bb) in enumerate(zip(A0,b0)):
        if bb>0 and op=='=' and all(w>0 for x,w in cs):
            for x,w in cs:norm[x]=i,w
    def rounded(y,c):
        y={i:Q(round(q*scale),scale) for i,q in y.items() if q}
        cost={k:round(w*scale) for k,w in c.items() if w}
        rc=projected(A0,b0,obj,labels,y,{k:Q(q,scale) for k,q in cost.items()});adj=Counter()
        # Unlinked residual-bucket variables have no fine norm row.
        # Raise their aggregation multiplier; repair the coarse variable
        # thereby affected using its own normalizer.
        for x,z in list(rc.items()):
            if z>0 and x not in norm:
                i,w=unlinked[x];y[i]=y.get(i,0)+z/w
                for xx,v in A0[i][0]:rc[xx]-=v*z/w
        for x,z in rc.items():
            if z>0:
                i,w=norm[x];adj[i]=max(adj[i],z/w)
        for i,q in adj.items():y[i]=y.get(i,0)+q
        return y,cost
    unlinked={x:(i,w) for i,((cs,op),bb) in enumerate(zip(A0,b0)) if bb==0 for x,w in cs if w>0 and x.startswith('f') and x not in norm}
    _,old=json.loads(lower.read_text());prior={(j,(a,b,tuple(p)),c) for j,(a,b),p,c,_ in old}
    seed=prior.copy();bestub=None
    known=set()
    if compact:
        pp=json.loads(lower.read_text())[0];known={k for k,x in labels.items() if x in pp}
    for it in range(100):
        y,cost=rounded(y,center if it==0 else proposed)
        eps=.035 if blend else (.15 if it==0 else .06) if phase else (.003 if lean else (.06 if H==11 else .23) if it==0 else .12)
        dist,n,arcs=oracle(cost,eps,H);ub=sum(q*b0[i] for i,q in y.items())-dist
        print(it,'unrestricted upper',float(ub),'priced arcs',len(arcs),flush=True)
        if bestub is None or ub<bestub:
            bestub=ub;center={k:Q(cost.get(k,0),scale) for k in labels};anchor=y.copy()
            path.write_text(json.dumps([{i:str(q) for i,q in y.items() if q},[[k,q] for k,q in cost.items() if q]],separators=(',',':'))+'\n')
            if ub<target:
                if lean or phase:file.with_name('eleven_upper_109.json').write_bytes(path.read_bytes())
                assert check(H)<target;return
        if compact and it==0:
            arcs=[(j,s,c) for j,s,c in arcs if j<2 or all((fine_axis(j-2,H),r,m) in known
                    for r,m in enumerate(masks(*s[:2],c,H)) if r>=6)]
        prior.update(arcs)
        ns,A,b=ns0.copy(),A0.copy(),b0.copy();flow=defaultdict(list);links=defaultdict(list)
        def ft(j):return 12+(j-12)%3 if phase and 12<=j<=98 else j
        visited=set()
        for i,(j,s,c) in enumerate(sorted(prior)):
            sig=(ft(j),s,c,ft(j+1),fine_axis(j-2,H) if j>=2 else -1)
            if phase and sig in visited:continue
            visited.add(sig)
            a,v,p=s;d=move(v,p,c);assert d is not None
            x=f'z{i}';ns['arc',j,s,c]=x;flow[ft(j),s].append((x,1))
            if j<108:flow[ft(j+1),(v,c,d)].append((x,-1))
            if j>=2:
                for r,m in enumerate(masks(a,v,c,H)):links[fine_axis(j-2,H),r,m].append((x,1))
        bounds={};objective=obj.copy()
        for i,(k,x) in enumerate(labels.items()):
            terms=links[k]+[(x,-1)];mult=30 if 8<=k[0]<=10 else 1
            for sign in (-1,1):
                art=f'u{i}_{sign}';ns['box',i,sign]=art;terms.append((art,sign))
                bounds[art]=(.002 if lean or phase else .015)*mult;objective[art]=sign*float(center[k])-.0001/mult
            A.append((terms,'='));b.append(0)
        for k,cs in flow.items():A.append((cs,'='));b.append(int(k==(0,start)))
        val,raw,v=solve(A,b,objective,ns,interior=True,bounds=bounds)
        print('restricted stabilized objective',val,flush=True)
        if not phase and val>=target and it%3==0:
            sub={k:x for k,x in ns.items() if x not in bounds and (not x.startswith('z') or v[x]>1e-6)}
            sub.update({k:x for k,x in ns.items() if k[0]=='arc' and k[1:] in seed})
            support=set(sub.values());thin=[([(x,w) for x,w in cs if x in support],op) for cs,op in A]
            try:val,_,v=solve(thin,b,obj,sub)
            except AssertionError:pass
            else:
                if val>=target-1e-8:
                    save(primal(thin,b,v),ns,lower.stem);assert replay(H)>=target;return
        y=dict(enumerate(raw[:len(A0)]))
        proposed=tighten(y,dict(zip(labels,raw[len(A0):])))
        if blend:
            # Average independent extreme master duals (also their core
            # multipliers). Verify the resulting mixture on all paths.
            if it==0:ym=dict(anchor);cm=dict(center)
            frac=.35
            ym={i:(1-frac)*ym.get(i,0)+frac*y.get(i,0) for i in y.keys()|ym.keys()}
            cm={k:(1-frac)*cm[k]+frac*q for k,q in proposed.items()}
            y=ym.copy();proposed=cm.copy()

if __name__=='__main__':
    import sys
    H=11 if '--eleven' in sys.argv else 9
    if '--corridor' in sys.argv:corridor_lower(float(sys.argv[-1]))
    elif '--build' in sys.argv:discover(H,'--compact' in sys.argv,'--lean-master' in sys.argv,'--phase-master' in sys.argv,'--blend' in sys.argv)
    else:check(H)
