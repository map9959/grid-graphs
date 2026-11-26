"""Bound with a small adaptive price basis; exact separated 13-row words."""
from .thirteen_hull import *

def run(H=13):
    stem='fifteen' if H==15 else 'fourteen'
    if H>=14:
        from . import fourteen_bound as fb
        ns0,A0,b0,obj,l,*_=(fb.core15 if H==15 else fb.core14)()
        def oracle(c,budget,paths=False,beam=False):return fb.oracle(c,budget,'paths' if paths else 'beam' if beam else None,H)
    else:
        ns0,A0,b0,obj,l=model(H)
        from .thirteen_local import overlaps
        for t in overlaps(l):A0.append((t,'='));b0.append(0)
        oracle=joint_oracle
    offsets=(0,H-9);blocks=[(o,9) for o in offsets];labs=layout(l,blocks);target=4107-H
    norm={};agg=[]
    for i,((cs,op),bb) in enumerate(zip(A0,b0)):
        if bb>0 and op=='=' and all(w>0 for x,w in cs):
            for x,w in cs:norm[x]=i,w
        if bb==0 and len({x[0] for x,w in cs})>1 and any(x[0] in 'fghij' and w>0 for x,w in cs):agg.append((i,cs))
    def events(word):
        ct=Counter()
        for j in range(107):
            ms=masks(*word[j:j+3],H)
            ct.update((o,fine_axis(j,H),r,m) for o in offsets for r,m in enumerate(ms[o:o+7]))
        return ct
    _,aa=json.loads(pathspec(H)[1].read_text());flow=defaultdict(dict);words={}
    for j,(a,b),p,c,q in aa:flow[j,(a,b,tuple(p))][c]=Q(q)
    start=pathspec(H)[0]
    while flow[0,start]:
        s=start;ps=[];w=[]
        for j in range(109):
            c=next(iter(flow[j,s]));ps.append((j,s,c));w.append(c);s=s[1],c,move(s[1],s[2],c)
        z=min(flow[j,s][c] for j,s,c in ps)
        for j,s,c in ps:
            flow[j,s][c]-=z
            if not flow[j,s][c]:del flow[j,s][c]
        words[tuple(w)]=events(w)
    def get(tag):
        if H>=14 and tag.startswith('new'):
            p=Path(f'target/{stem}_{tag[3:]}.json')
            return {tuple(k):q for k,q in json.loads(p.read_text())[1]} if p.exists() else {}
        if H==15:
            p=Path(f'target/fourteen_{tag}.json') if tag!='saved' else file.with_name('fourteen_upper_109.json')
            cc=json.loads(p.read_text())[1]
        else:cc=json.loads((Path(f'target/thirteen_{tag}.json') if tag!='saved' else file.with_name('thirteen_upper_109.json')).read_text())[2]
        if H==13:return {tuple(k):q for k,q in cc}
        c=Counter()
        for (o,h,r,m),q in cc:
            rr=o+r;off=0 if o==0 or rr<H-9 else H-9
            for z in [h]+[fine_axis(j,H) for j in (H-3,109-H) if fine_axis(j,H-1)==h]:c[off,z,rr-off,m]+=q
        return c
    optimize='--centered' in __import__('sys').argv
    ref=get(('newmain' if optimize or '--adaptive' in __import__('sys').argv else 'saved') if H>=14 else 'resumed') or get('saved');baseobj=Counter(obj)
    for k,v in ref.items():baseobj[labs[k]]+=v/scale
    basis=[];seen=set()
    localized='--localized' in __import__('sys').argv
    def sample_arcs(arcs,cost):
        # Backward pricing on a discovered *feasible* subgraph; keep the
        # best suffix through each state and draw small-regret words.
        import random
        g=defaultdict(list)
        for j,(a,b,p),v in arcs:
            d=b,v,move(b,p,v);ms=masks(a,b,v,H);h=fine_axis(j-2,H)
            z=sum(cost.get((o,h,r,m),0) for o in offsets for r,m in enumerate(ms[o:o+7])) if j>=2 else 0
            g[j].append(((a,b,p),d,v,z))
        val={};hist=[];rng=random.Random(731)
        for j in reversed(range(109)):
            choices=defaultdict(list)
            for s,d,v,z in g[j]:
                if j==108 or d in val:choices[s].append((z+val.get(d,0),v,d))
            for opts in choices.values():opts.sort()
            val={s:opts[0][0] for s,opts in choices.items()};hist.append(choices)
        for i in range(90):
            s=start;w=[]
            for layer in reversed(hist):
                opts=layer[s];p=opts[0][0];lim=scale*(.5 if i%3 else .05)/109
                opts=[z for z in opts if z[0]<=p+lim]
                _,v,s=rng.choice(opts);w.append(v)
            w=tuple(w);words[w]=events(w)
    regular='--regular' in __import__('sys').argv
    if regular and H==15:
        ref=get('newbalanced');baseobj=Counter(obj)
        for k,v in ref.items():baseobj[labs[k]]+=v/scale
    if localized or optimize or regular:
        for tag in ('newmain','newrestart','newbox','saved'):
            cost=get(tag)
            if not cost:continue
            _,_,aa=oracle(cost,10**13,beam=True);sample_arcs(aa,cost)
    if '--translated' in __import__('sys').argv:
        # Each known price vector can be applied to any contiguous substrip.
        # These are master directions; final validity is checked from scratch.
        for h0,oldstem in ((9,'nine'),(11,'eleven'),(13,'thirteen'))+(((14,'fourteen'),) if H==15 else ()):
            data=json.loads(file.with_name(oldstem+'_upper_109.json').read_text());pr=Counter()
            if h0>=13:
                for (o,h,r,m),q in data[2 if h0==13 else 1]:pr[h,o+r,m]+=q
            else:pr.update({tuple(k):q for k,q in data[1]})
            oldphase={fine_axis(j,H):fine_axis(j,h0) for j in range(107)}
            for shift in range(H-h0+1):
                for flip in (False,True):
                    delta={}
                    for k in labs:
                        o,h,r,m=k;row=o+r-shift
                        if o!= (0 if o+r<7 else H-9) or not 0<=row<h0-2:continue
                        z=pr[oldphase[h],h0-3-row if flip else row,((m&7)<<6)|(m&56)|((m&448)>>6) if flip else m]
                        if z:delta[k]=z
                    basis.append(delta)
    def dot(c,ct):return sum(c.get(k,0)*v for k,v in ct.items())/scale
    best=float('inf')
    for it in range(100):
        for tag in (('main','box','balanced','restart','prox','saved','feature_candidate') if H==15 else ('resumed','trial_11_wide','trial_9_wide','diverse'))+(('newmain','newbox','newalt','newrestart','newbalanced','newprox') if H>=14 else ()):
            c=get(tag)
            if not c:continue
            key=hash(tuple(sorted(c.items())))
            if key in seen:continue
            seen.add(key);diff={k:c.get(k,0)-ref.get(k,0) for k in labs}
            if any(diff.values()):
                basis.append(diff)
                if localized and len(basis)<200:
                    local=defaultdict(dict)
                    for k,q in diff.items():
                        if q:
                            o,h,r,m=k;ph=(min(h,18-h)//3 if h<8 or 10<h<19 else 3 if h>=19 else 4)
                            local[(o+r)//3,ph][k]=q
                    basis.extend(local.values())
        A=A0.copy();b=b0.copy();ns=ns0.copy();objective=baseobj.copy()
        for i,(w,ct) in enumerate(words.items()):
            x=f'w{i}';ns['word',i]=x;objective[x]=-dot(ref,ct)
        A.append(([(f'w{i}',1) for i in range(len(words))],'='));b.append(1)
        for j,delta in enumerate(basis):
            row=Counter()
            for k,v in delta.items():row[labs[k]]-=v
            cs=[(x,v/scale) for x,v in row.items() if v]+[(f'w{i}',dot(delta,ct)) for i,ct in enumerate(words.values())]
            for s in (-1,1):
                x=f't{j}_{s}';ns['box',j,s]=x;cs.append((x,s));objective[x]=-.32 if regular else -1.5
            A.append((cs,'='));b.append(0)
        val,raw,sol=solve(A,b,objective,ns,interior=True)
        y={i:Q(round(q*scale),scale) for i,q in enumerate(raw[:len(A0)]) if q}
        c=Counter(ref)
        for delta,coef in zip(basis,raw[len(A0)+1:]):
            coef=Q(round(coef*scale),scale)
            for k,v in delta.items():
                if v:c[k]+=coef*v
        cost={k:q.__floor__() for k,q in c.items() if q}
        rc=projected(A0,b0,obj,labs,y,{k:Q(q,scale) for k,q in cost.items()})
        for i,cs in reversed(agg):
            z=max([rc[x]/w for x,w in cs if w>0 and x not in norm]+[0])
            if z>0:
                y[i]=y.get(i,0)+z
                for x,w in cs:rc[x]-=w*z
        adj=Counter()
        for x,z in rc.items():
            if z>0:
                i,w=norm[x];adj[i]=max(adj[i],z/w)
        for i,q in adj.items():y[i]=y.get(i,0)+q
        assert max(projected(A0,b0,obj,labs,y,{k:Q(q,scale) for k,q in cost.items()}).values())<=0
        rhs=sum(q*b0[i] for i,q in y.items());budget=((rhs-target)*scale).__floor__()
        d,n,arcs=oracle(cost,budget,paths=True);ub=rhs-d
        print(it,'basis',len(basis),'words',len(words),'master',val,'exact upper',float(ub),flush=True)
        if H>=14 and ub<best:
            best=ub;Path(f'target/{stem}_feature_candidate.json').write_text(json.dumps([{i:str(q) for i,q in y.items() if q},[[k,q] for k,q in cost.items() if q],budget],separators=(',',':')))
            if regular and it:
                ref=cost;baseobj=Counter(obj)
                for k,v in ref.items():baseobj[labs[k]]+=v/scale
        if ub<target:
            data=[{i:str(q) for i,q in y.items() if q},[[k,q] for k,q in cost.items() if q],budget]
            if H>=14:
                file.with_name(stem+'_upper_109.json').write_text(json.dumps(data,separators=(',',':'))+'\n');assert fb.check(H)<target
            else:
                path.write_text(json.dumps([blocks]+data,separators=(',',':'))+'\n');assert check()<target
            return
        if not arcs:_,_,arcs=oracle(cost,budget,beam=True)
        layers=defaultdict(list)
        for j,s,c in arcs:layers[j].append((s,c))
        dp={start:0};hist=[]
        for j in range(109):
            nd={};pr={};h=fine_axis(j-2,H)
            for s,c in layers[j]:
                if s not in dp:continue
                z=dp[s];a,v,p=s;dst=v,c,move(v,p,c)
                if j>=2:
                    ms=masks(a,v,c,H);z+=sum(cost.get((o,h,r,m),0) for o in offsets for r,m in enumerate(ms[o:o+7]))
                if dst not in nd or z<nd[dst]:nd[dst]=z;pr[dst]=s,c
            dp=nd;hist.append(pr)
        for dst in sorted(dp,key=dp.get)[:30]:
            w=[]
            for pr in reversed(hist):dst,c=pr[dst];w.append(c)
            w=tuple(reversed(w));words[w]=events(w)
        if H>=14 and '--adaptive' in __import__('sys').argv:
            # Direction separating the current core from the priced-word
            # mixture. Only its dot products are used in the small master.
            emitted=Counter()
            for i,(w,ct) in enumerate(words.items()):
                q=sol.get(f'w{i}',0)
                if q>1e-8:
                    for k,z in ct.items():emitted[k]+=q*z
            delta={}
            for k,x in labs.items():
                mult=30 if 8<=k[1]<=10 else 1
                residual=(emitted[k]-sol[x])/mult
                if abs(residual)>1e-5:
                    delta[k]=round(scale*.03*max(-1,min(1,residual)) /mult)
            if delta:basis.append(delta)

if __name__=='__main__':
    import sys
    run(15 if '--fifteen' in sys.argv else 14 if '--fourteen' in sys.argv else 13)
