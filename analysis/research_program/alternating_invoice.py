"""Upper-bound a two-phase slope by separate periodic arm and diagonal maxima."""
import re
from collections import Counter
from functools import lru_cache
from itertools import product

from .temperley_diagonal import saturated,sides
from .temperley_synthesis import DIR,Formula,polynomial,solve


def bound(a,b,offset,seconds=2,band=False,slack=0,flux_only=False,unresolved=None,budgets=None):
    f,cs=polynomial(5,a,b,stagger=True,offset=offset,band=band)
    inv={v:k for k,v in f.names.items()}
    weights={v:3*cs[1][v]-2*cs[0][v]-cs[2][v] for v in set().union(*cs)}
    def region(x):
        g=inv[x][0][0][:3]
        return (1,1,0) if band and g[:2]==(1,1) and abs(g[2])==2 else g
    bg={(1,1,-1),(1,1,1)}
    groups=sorted([(0,1,0),(2,1,0),(1,0,0),(1,2,0),(1,1,0)])
    atom={}
    labels={}
    scores={g:[] for g in groups}
    pure={}
    for v,k in inv.items():
        if k[0]=='score':
            labels[v]={region(x) for x in k[1]}-bg
            if weights.get(v,0):
                if labels[v]:
                    assert len(labels[v])==1 and weights[v]==1
                    scores[next(iter(labels[v]))].append(v)
                else:
                    pure[v]=k[1]
        else:
            labels[v]={region(v)}-bg
    rows=[]
    for d in saturated():
        masks=sides(lambda i,j:d[i%12,j%12],a,b)
        if all(not sum((-1)**h for h in range(12) if m>>h&1) for m in masks[:2]):
            rows.append(d)
    assert len(rows)==36
    if band:
        # Six different free diagonal subtiles: offsets -1,0,+1,
        # each in two longitudinal phases. Grouping score bits does not
        # identify their matching variables.
        kinds={k[0][0] for k in inv.values() if k[0]!='score'}
        free={k for k in kinds if k[:2]==(1,1) and k[2] in (-2,0,2)}
        assert len(free)==6
    for v,k in inv.items():
        if labels[v] or k[0]=='score':
            continue
        (kind,i,j),e=k
        _,_,sign,pi,pj=kind
        atom[v]=(sign,tuple(d[(a+(1-pi)*6+i)%12,(b+(1-pj)*6+j)%12]==DIR[e] for d in rows))
    local={g:[] for g in groups}
    for clause in f.clauses:
        xs=re.findall(r'x\d+',clause)
        regs=set().union(*(labels[x] for x in xs))
        if len(regs)!=1 or not regs.issubset(groups):continue
        g=next(iter(regs))
        if any(inv[x][0]=='score' and x not in scores[g] for x in xs):continue
        local[g].append(tuple((x,f"(not {x})" in clause) for x in xs))
    def val(x,lo,hi):
        s,vals=atom[x]
        return vals[lo if s<0 else hi]
    for g in groups:
        signs={atom[v][0] for cl in local[g] for v,_ in cl if v in atom}
        allowed={-1,1} if g==(1,1,0) else {-1} if g in ((0,1,0),(1,2,0)) else {1}
        assert signs<=allowed
    decisions=Counter()
    flux_skips=0
    @lru_cache(24)
    def maximize(g,clauses,threshold):
        names=set(x for cl in clauses for x,neg in cl)|set(scores[g])
        p=Formula()
        p.names={v:v for v in names}
        for cl in clauses:
            if not cl:return -10000
            p.clause(*(f"(not {v})" if neg else v for v,neg in cl))
        text=p.smt()
        if threshold is not None:
            # One decision instead of optimizing an already insufficient
            # diagonal. Return a conservative bound if the query times out.
            if threshold>len(scores[g]):return len(scores[g])
            query=text+"\n(assert ((_ at-least "+str(threshold)+") "+" ".join(scores[g])+"))"
            ans,_=solve(query,seconds)
            if ans=="unknown":
                ans,_=solve(query,4*seconds,"(then simplify propagate-values solve-eqs simplify sat)")
            decisions[ans]+=1
            return threshold-1 if ans=="unsat" else len(scores[g])
        low,high=0,len(scores[g])
        while low<high:
            mid=(low+high+1)//2
            ans,_=solve(text+"\n(assert ((_ at-least "+str(mid)+") "+" ".join(scores[g])+"))",seconds)
            if ans=='unsat':high=mid-1
            else:
                if ans=='unknown':return high
                low=mid
        return high
    @lru_cache(None)
    def charge(g,lo,hi,threshold=None):
        cls=set()
        for cl in local[g]:
            if any(val(v,lo,hi)!=neg for v,neg in cl if v in atom):continue
            cls.add(tuple((v,neg) for v,neg in cl if v not in atom))
        return maximize(g,tuple(sorted(cls)),threshold)
    hist=Counter()
    # Stream the instantiated clauses. Caching all 1,296 wide diagonal
    # instances as Python tuples wastes memory; small arm queries repeat.
    target=74+12*offset+24*int(band)-slack
    for lo,hi in product(range(len(rows)),repeat=2):
        bulk=sum(weights[v] for v,sig in pure.items() if not any(val(x,lo,hi) for x in sig))
        total=24+bulk
        for g in sorted(groups,key=lambda g:g==(1,1,0)):
            needs_lo=g in ((0,1,0),(1,2,0),(1,1,0))
            needs_hi=g in ((2,1,0),(1,0,0),(1,1,0))
            if band and g==(1,1,0):
                from .diagonal_cylinder import band_flux_bound
                flux=band_flux_bound(rows[lo],rows[hi],a,b,expected=len(scores[g]))
                if budgets is not None:
                    budgets[lo,hi]=band_flux_bound(rows[lo],rows[hi],a,b,ledger=True)-3*(target-total)
                if flux<target-total or flux_only:
                    amount=flux
                    flux_skips+=int(flux<target-total)
                else:
                    amount=min(flux,charge(g,lo,hi,target-total))
            else:
                amount=charge(g,lo if needs_lo else 0,hi if needs_hi else 0)
            total+=amount
            if amount<0:break
        hist[total]+=1
        if unresolved is not None and total>=target:
            unresolved.append((lo,hi))
    print("split",a,b,"offset",offset,"layout pairs",sum(hist.values()),
           "band",bool(band),"upper bound",max(hist),"target",target,
           "flux exclusions",flux_skips,"queries",dict(decisions),"unexcluded",sum(n for v,n in hist.items() if v>=target),flush=True)
    return hist


if __name__=='__main__':
    import sys
    bound(*(int(x) for x in sys.argv[1:]))
