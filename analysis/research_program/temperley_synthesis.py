"""Synthesize exact-score templates from local matching and score constraints."""
import argparse
import ctypes
from collections import Counter
from functools import lru_cache
from itertools import product


class Formula:
    def __init__(self):
        self.names = {}
        self.clauses = set()

    def var(self, tag):
        return self.names.setdefault(tag, f"x{len(self.names)}")

    def clause(self, *terms):
        self.clauses.add("(assert (or " + " ".join(sorted(terms)) + "))")

    def pb(self, counts, target):
        total = sum(counts.values())
        if total < target:
            self.clauses.add("(assert false)")
        elif target > 0:
            names = sorted(counts)
            coeff = " ".join(str(counts[v]) for v in names)
            self.clauses.add(f"(assert ((_ pbge {target} {coeff}) {' '.join(names)}))")

    def smt(self):
        return "\n".join([*(f"(declare-const {v} Bool)" for v in self.names.values()),
                          *sorted(self.clauses)])


def solve(text, seconds, tactic="(then simplify pb2bv bit-blast sat)"):
    z = ctypes.CDLL("libz3.so.4")
    ptr = ctypes.c_void_p
    z.Z3_mk_config.restype = z.Z3_mk_context.restype = ptr
    z.Z3_mk_context.argtypes = [ptr]
    ctx = z.Z3_mk_context(z.Z3_mk_config())
    z.Z3_eval_smtlib2_string.argtypes = [ptr,ctypes.c_char_p]
    z.Z3_eval_smtlib2_string.restype = ctypes.c_char_p
    def evaluate(s):
        return z.Z3_eval_smtlib2_string(ctx,s.encode()).decode().strip()
    ans = evaluate(f"(set-option :timeout {1000*seconds})\n{text}\n(check-sat-using {tactic})")
    model = evaluate("(get-model)") if ans=="sat" else None
    z.Z3_del_context.argtypes = [ptr]
    z.Z3_del_context(ctx)
    return ans,model


DIR = ((0,1),(1,0),(0,-1),(-1,0))


def instance(base,a,b,t,F,rich=False,stagger=False,band=False,wind=False,*,replay=None):
    """One representative per tile/site. A and B fill the strict triangles."""
    widths = [b]+[6]*t+[2*base-1-b]
    heights = [a]+[6]*t+[2*base-1-a]
    side = sum(widths)
    @lru_cache(None)
    def tag(r,c):
        if min(r,c)<0 or max(r,c)>=side or (r,c)==(0,0):
            return None
        i,j=0,0
        while r>=heights[i]:
            r-=heights[i]
            i+=1
        while c>=widths[j]:
            c-=widths[j]
            j+=1
        typ = lambda x: 0 if x==0 else (2 if x==t+1 else 1)
        kind=(typ(i),typ(j), (i>j)-(i<j) if typ(i)==typ(j)==1 else 0)
        if band and typ(i)==typ(j)==1 and abs(i-j)==1:
            kind=(1,1,2*(i-j))
        if wind and typ(i)==typ(j)==1:
            kind=(*kind,(i+j>t+1)-(i+j<t+1))
        if rich:
            def end(z):
                return 1 if z==1 else -1 if z==t else 0
            # Give the two ends of each arm their own tiles; the running
            # diagonal may use distinct adapters in its two outermost cells.
            if typ(i)==typ(j)==1:
                kind=(*kind,end(i) if i==j else 0)
            elif typ(i)==1 or typ(j)==1:
                kind=(*kind,end(i if typ(i)==1 else j))
        if stagger:
            kind=(*kind,i%2 if typ(i)==1 else 0,j%2 if typ(j)==1 else 0)
        return kind,r,c
    def arrow(p,d):
        return F.var((p,d))
    def neg(v):
        return f"(not {v})"
    if replay is not None:
        from .temperley_cross import score
        d={}
        for r,c in product(range(side),repeat=2):
            p=tag(r,c)
            if p:
                chosen=[DIR[e] for e in range(4) if F.names[p,e] in replay]
                assert len(chosen)==1
                d[r,c]=chosen[0]
        assert all(d.get((r+x,c+y))==(-x,-y) for (r,c),(x,y) in d.items())
        return score(d,side)
    counts=Counter()
    for r,c in product(range(side),repeat=2):
        p = tag(r,c)
        if p is not None:
            arrows=[arrow(p,d) for d in range(4)]
            F.clause(*arrows)
            for d,x in enumerate(arrows):
                for y in arrows[:d]:
                    F.clause(neg(x),neg(y))
                u,v=DIR[d]
                q=tag(r+u,c+v)
                F.clause(neg(x),*([arrow(q,(d+2)%4)] if q else []))
        if r%2==c%2==0:
            # A vertical midpoint must not be paired horizontally, and vice versa.
            wrong=[]
            for d,(u,v) in enumerate(DIR):
                q=tag(r+u,c+v)
                if q:
                    wrong.extend(arrow(q,e) for e in ((d+1)%4,(d+3)%4))
            sig=tuple(sorted(wrong))
            f=F.var(("score",sig))
            for x in wrong:
                F.clause(neg(f),neg(x))
            F.clause(f,*wrong)
            counts[f]+=1
    return counts


def polynomial(base,a,b,rich=False,stagger=False,band=False,wind=False,offset=0):
    f=Formula()
    # Only tile contexts are used as variables; no large board is optimized.
    start = (7 if wind else 5 if rich or band else 3)+offset
    step=2 if stagger or wind else 1
    counts=[instance(base,a,b,start+step*i,f,rich,stagger,band,wind) for i in range(4)]
    keys=set().union(*counts)
    assert all(counts[3][v]-3*counts[2][v]+3*counts[1][v]-counts[0][v]==0 for v in keys)
    return f,counts


def lower(f, weighted, rhs):
    c=Counter()
    for v,w in weighted.items():
        if w>0:
            c[v]=w
        if w<0:
            c[f"(not {v})"]=-w
            rhs-=w
    f.pb(c,rhs)


def force_rails(f,a,b,wind=False,axes=None):
    """At full area coefficient both triangular periodic backgrounds saturate."""
    from .temperley_diagonal import saturated
    layouts=set()
    for d in saturated():
        if all(d[i,j]==d[(i+6)%12,j]==d[i,(j+6)%12] for i,j in d):
            layouts.add(tuple(DIR.index(d[(a+i)%12,(b+j)%12])
                              for i,j in product(range(6),repeat=2)))
    assert len(layouts)==24
    for sign,other in product([-1,1],[-1,1] if wind else [0]):
        choices=[]
        for layout in sorted(layouts):
            if axes is not None:
                # At an F vertex, its own arrow runs longitudinally.
                directions=[]
                for i,j in product(range(6),repeat=2):
                    if (a+i)%2 or (b+j)%2:
                        continue
                    if all(layout[((i+x)%6)*6+(j+y)%6]%2==d%2
                           for d,(x,y) in enumerate(DIR)):
                        directions.append(layout[i*6+j]%2)
                assert len(directions)==3 and len(set(directions))==1
                if directions[0]!=axes[sign,other]:
                    continue
            v=f.var(("rail",sign,other,layout))
            choices.append(v)
            for (i,j),direction in zip(product(range(6),repeat=2),layout):
                k=(1,1,sign,other) if wind else (1,1,sign)
                candidates=[(k,i,j),((*k,0),i,j)]
                name=next(f.names[(p,direction)] for p in candidates if (p,direction) in f.names)
                f.clause(f"(not {v})",name)
        f.clause(*choices)


def stagger_rails(f,a,b,rich):
    from .temperley_diagonal import saturated,sides
    layouts=list(saturated())
    assert len(layouts)==96
    inverse={name:key for key,name in f.names.items()}
    bulk_by_phase={}
    for sign in [-1,1]:
        # Generator order: three phases, four orientation bits, two axes.
        modes=[f.var(("rail mode",sign,l)) for l in range(6)]
        bits=[f.var(("rail direction",sign,l)) for l in range(4)]
        f.clause(*modes)
        # Each triangle meets two adjacent repeating physical boundary
        # strips. Per 12 sites there is no net checkerboard flux to either
        # strip: the physical edge is closed and the period ends cancel.
        for l,d in enumerate(layouts):
            masks=sides(lambda i,j:d[i%12,j%12],a,b)
            if any(sum((-1)**h for h in range(12) if m>>h&1) for m in masks[:2]):
                h=(l//2)%16
                f.clause(f"(not {modes[(l//32)*2+l%2]})",
                         *(f"(not {u})" if h>>idx&1 else u for idx,u in enumerate(bits)))
        for i,j in product(range(12),repeat=2):
            typ=(1,1,sign)+((0,) if rich else ())+((1+i//6)%2,(1+j//6)%2)
            p=typ,i%6,j%6
            for mode,v in enumerate(modes):
                dirs=[DIR.index(layouts[(mode//2)*32+h*2+mode%2][(a+i)%12,(b+j)%12])
                      for h in range(16)]
                if len(set(dirs))==1:
                    f.clause(f"(not {v})",f.names[p,dirs[0]])
                else:
                    bit=next(b for b in range(4) if all(dirs[h]==dirs[h&(1<<b)] for h in range(16)))
                    u=bits[bit]
                    f.clause(f"(not {v})",u,f.names[p,dirs[0]])
                    f.clause(f"(not {v})",f"(not {u})",f.names[p,dirs[1<<bit]])
        # Primal versus dual pairing on a midpoint depends only on rail
        # phase/axis, never on the four longitudinal orientation choices.
        for name,key in inverse.items():
            if key[0]!="score":
                continue
            sig=key[1]
            here=[]
            for x in sig:
                (kind,i,j),e=inverse[x]
                if kind[:3]!=(1,1,sign) or len(kind)!=5+int(rich) or (rich and kind[3]!=0):
                    continue
                y,z=kind[-2:]
                here.append(((a+(1-y)*6+i)%12,(b+(1-z)*6+j)%12,e))
            if not here:
                continue
            if len(here)==len(sig):
                bulk_by_phase[name]=[]
            for mode,v in enumerate(modes):
                d=layouts[(mode//2)*32+mode%2]
                invalid=any(d[r,c]==DIR[e] for r,c,e in here)
                if invalid or len(here)==len(sig):
                    f.clause(f"(not {v})",f"(not {name})" if invalid else name)
                if len(here)==len(sig) and not invalid:
                    bulk_by_phase[name].append(v)
    return bulk_by_phase


def run(base,a,b,seconds,loss,rich=False,stagger=False,band=False,wind=False,slope_loss=0,offset=0,split_modes=False,tactic="(then simplify pb2bv bit-blast sat)"):
    f,cs=polynomial(base,a,b,rich,stagger,band,wind,offset)
    k=(base-2)//3+(7 if wind else 5 if rich or band else 3)+offset
    diff=lambda c,d:Counter({v:c[v]-d[v] for v in set(c)|set(d)})
    first=diff(cs[1],cs[0])
    step=2 if stagger or wind else 1
    second=diff(diff(cs[2],cs[1]),first)
    if stagger and not wind:
        # Both periodic backgrounds are fixed at equality: the second
        # difference is exactly 24, independent of their direction bits.
        bulk=stagger_rails(f,a,b,rich)
        coeff=diff(first,second)
        for score,modes in bulk.items():
            w=coeff.pop(score,0)
            for mode in modes:
                coeff[mode]+=w
        rhs=step*(6*k+3*step+7)-slope_loss-24
        for sign in [-1,1]:
            modes=[f.names["rail mode",sign,i] for i in range(6)]
            mn=min(coeff[v] for v in modes)
            for v in modes:
                coeff[v]-=mn
            rhs-=mn
        lower(f,coeff,rhs)
    else:
        lower(f,second,6*step**2)
        lower(f,first,step*(6*k+3*step+7)-slope_loss)
    lower(f,cs[0],3*k*k+7*k-loss)
    if not stagger:
        force_rails(f,a,b,wind)
    text=f.smt()
    if split_modes:
        assert stagger and not wind
        tally=Counter()
        for m,n in product(range(6),repeat=2):
            extra=f"(assert {f.names['rail mode',-1,m]})(assert {f.names['rail mode',1,n]})"
            ans,model=solve(text+"\n"+extra,seconds,tactic)
            tally[ans]+=1
            if ans=="sat":
                break
        else:
            ans="unknown" if tally["unknown"] else "unsat"
        print("rail mode pairs:",dict(tally),flush=True)
    else:
        ans,model=solve(text,seconds,tactic)
    print(f"base={base} split={a},{b} vars={len(f.names)} clauses={len(f.clauses)} status={ans}",flush=True)
    if model:
        import re
        on=set(re.findall(r"\(define-fun (x\d+) \(\) Bool\s+true\)",model))
        predicted=[sum(w for v,w in c.items() if v in on) for c in cs]
        start=k-(base-2)//3
        actual=[instance(base,a,b,start+i*step,f,rich,stagger,band,wind,replay=on)
                for i in range(5)]
        assert predicted==actual[:4] and actual[4]==3*actual[3]-3*actual[2]+actual[1]
        print("replayed tree scores:",actual,flush=True)
    return ans


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    for name,default in (("base",5),("a",4),("b",4),("seconds",20),("loss",0)):
        parser.add_argument("--"+name,type=int,default=default)
    parser.add_argument("--rich",action="store_true")
    parser.add_argument("--stagger",action="store_true")
    parser.add_argument("--band",action="store_true")
    parser.add_argument("--wind",action="store_true")
    parser.add_argument("--slope-loss",type=int,default=0)
    parser.add_argument("--offset",type=int,choices=(0,1),default=0)
    parser.add_argument("--split-modes",action="store_true")
    parser.add_argument("--tactic",default="(then simplify pb2bv bit-blast sat)")
    run(**vars(parser.parse_args()))
