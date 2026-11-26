"""Combine valid core multipliers; cut the small mixing LP with actual strip words."""
from .thirteen_bound import *
from .side28_score import solve

def run(H=13):
    stem='fifteen' if H==15 else 'fourteen'
    if H>=14:
        from . import fourteen_bound as fb
        ns,A,b,obj,l,*_=(fb.core15 if H==15 else fb.core14)(True)
        def oracle(c,budget,paths=False,beam=False):return fb.oracle(c,budget,'paths' if paths else 'beam' if beam else None,H)
        files=[stem+'_'+s for s in ('main','box','alt','restart','prox','balanced','feature_candidate','reflect','elastic','level')]
    else:
        ns,A,b,obj,l=model(H)
        from .thirteen_local import overlaps
        for t in overlaps(l):A.append((t,'='));b.append(0)
        oracle=joint_oracle
        files=('thirteen_trial_9_wide','thirteen_trial_11_wide','thirteen_resumed','thirteen_diverse')
    offsets=(0,H-9);labs=layout(l,[(o,9) for o in offsets]);bank=[];seen=set();cuts=[];target=4107-H
    for it in range(80):
        for f in files:
            pp=Path('target/'+f+'.json')
            if not pp.exists():continue
            txt=pp.read_text();finger=hash(txt)
            if finger in seen:continue
            data=json.loads(txt);yy,cc=data[:2] if H>=14 else data[1:3];seen.add(finger)
            y={int(i):Q(q) for i,q in yy.items()};c={tuple(k):v for k,v in cc}
            assert max(projected(A,b,obj,labs,y,{k:Q(q,scale) for k,q in c.items()}).values())<=0
            bank.append((y,c,sum(q*b[i] for i,q in y.items())))
        N=len(bank)
        if not cuts or it%5==0:weights=[Q(1,N)]*N
        else:
            names={i:f'a{i}' for i in range(N)};vs=list(names.values());names[N]='t'
            M=[([(x,1) for x in vs],'=')];rhs=[1]
            for w in cuts:
                M.append(([(x,float(bb-4090-Q(sum(v*c.get(k,0) for k,v in w.items()),scale))) for x,(_,c,bb) in zip(vs,bank)]+[('t',-1)],'<='));rhs.append(0)
            val,_,raw=solve(M,rhs,{'t':-1},names)
            weights=[Q(raw[x]).limit_denominator(10000) for x in vs]
            assert min(weights)>=0;weights=[q/sum(weights) for q in weights]
        Y=Counter();C=Counter();core_rhs=0
        for q,(y,c,bb) in zip(weights,bank):
            if q:
                core_rhs+=q*bb
                for i,v in y.items():Y[i]+=q*v
                for k,v in c.items():C[k]+=q*v
        cost={k:q.__floor__() for k,q in C.items()};budget=((core_rhs-target)*scale).__floor__()
        d,n,arcs=oracle(cost,budget,paths=True);ub=core_rhs-d
        print(it,'candidates',N,'upper',float(ub),'arcs',len(arcs),flush=True)
        if ub<target:
            data=[{i:str(q) for i,q in Y.items() if q},[[k,q] for k,q in cost.items() if q],budget]
            if H>=14:
                file.with_name(stem+'_upper_109.json').write_text(json.dumps(data+[1],separators=(',',':'))+'\n');assert fb.check(H)<target
            else:path.write_text(json.dumps([[(0,9),(4,9)]]+data,separators=(',',':'))+'\n');assert check()<target
            return
        if not arcs:
            _,_,arcs=oracle(cost,budget,beam=True)
        # Paths-mode or beam-mode returns a subgraph. Extract its minimum
        # using actual joined states and both prices. Add its event counts.
        layers=defaultdict(list)
        for j,s,c in arcs:layers[j].append((s,c))
        dp={pathspec(H)[0]:0};hist=[]
        for j in range(109):
            nd={};pred={};h=fine_axis(j-2,H)
            for s,c in layers[j]:
                if s not in dp:continue
                a,v,p=s;dst=v,c,move(v,p,c);ms=masks(a,v,c,H)
                z=dp[s]+(sum(cost.get((o,h,r,m),0) for o in offsets for r,m in enumerate(ms[o:o+7])) if j>=2 else 0)
                if dst not in nd or z<nd[dst]:nd[dst]=z;pred[dst]=(s,c)
            dp=nd;hist.append(pred)
        for dst in sorted(dp,key=dp.get)[:8]:
            w=Counter()
            for j in reversed(range(109)):
                dst,c=hist[j][dst]
                if j>=2:
                    ms=masks(*dst[:2],c,H);w.update((o,fine_axis(j-2,H),r,m) for o in offsets for r,m in enumerate(ms[o:o+7]))
            if w not in cuts:cuts.append(w)

if __name__=='__main__':
    import sys
    run(15 if '--fifteen' in sys.argv else 14 if '--fourteen' in sys.argv else 13)
