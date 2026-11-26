"""Physically refill 39-step width-eight pieces when testing uniform seams.

Keep each reference clause if (i) its variables lift together, or (ii)
it is a clause of a common shortened strip. New fills need not be copies.
"""
from pathlib import Path
from itertools import product
from array import array
from inspect import getclosurevars
import json,subprocess,sys
from .core413_seams import source,position,D
from .defect_window import window,table
from .two_gap_board import Stream

def test(ys,xs,budget):
    from pysat.solvers import Solver
    n=413;H=8;ts,cs=source();rev={t:z for z,t in ts.items()}
    marks=array('I');marks.frombytes((D/'marks.bin').read_bytes())
    arcs=array('I');arcs.frombytes((D/'arcs.bin').read_bytes())
    charges=table(n)
    segs=[(0,153,174)] if ys else []
    segs+=({'L':[(1,12,19)],'R':[(1,360,394)],'LR':[(1,12,19),(1,360,394)],'N':[]}[xs])
    pumped=set();baseclauses=[];startnv=2716317;nv=startnv
    def zid(t):
        nonlocal nv
        if t in rev:return rev[t]
        k,i,j,*rest=t
        if k=='v':z=marks[n*i+j]
        elif k=='a':z=arcs[4*(n*i+j)+rest[0]]
        else:nv+=1;z=nv
        assert z;rev[t]=z;return z
    for a,s,cut in segs:
        for far in (False,True):
            dom={((j,i) if a==0 else (i,j)) for j in range(s-5,s+45)
                 for r in range(H) for i in [n-1-r if far else r]}
            def emit(f,bit,flags):
                vp=getclosurevars(bit).nonlocals['vp']
                ids=[0]+[zid(vp.obj(z)) for z in range(1,vp.top+1)]
                for c in f.clauses:
                    mapped=tuple(sorted(ids[v] if v>0 else -ids[-v] for v in c))
                    pumped.add(mapped)
                for i,j in dom:
                    h=min(i,j,n-1-i,n-1-j)
                    if h in (0,1):
                        v=zid(('v',i,j));pumped.add(tuple(sorted((-rev['frame',],v if h==0 else -v))))
            window(n,'rim',1,charges,want=False,domain=dom,turn_domain=set(),emit=emit)
    cuts=[(a,k) for a,s,k in segs]
    def unchanged(t):
        if t[0] not in ('a','v'):return True
        i,j=t[1:3]
        for a,s,k in segs:
            v=(i,j)[a];w=(i,j)[1-a]
            if min(w,n-1-w)>=H:continue
            if t[0]=='v' and s<v<s+38:return False
            if t[0]=='a' and s<=v<s+39 and not(v==s and t[3]==(3 if a==0 else 2)):return False
        return True
    unchanged_id={z:unchanged(t) for z,t in ts.items()}
    omit=0;recover=0
    for c in cs:
        tt=[ts[abs(v)] for v in c]
        ok=all(unchanged_id[abs(v)] for v in c)
        if ok:
            for a,k in cuts:
                coords=[x for t in tt if (x:=position(t,a)) is not None]
                if coords and min(coords)<k<=max(coords):ok=False;break
        if ok:baseclauses.append(c)
        elif tuple(sorted(c)) in pumped:recover+=1
        else:omit+=1
    label=f'pump_{int(ys)}{xs}'+('_all' if '--all' in sys.argv else '');p=D/(label+'.cnf')
    # All common overlap inside each physical strip uses one set of variables.
    # No extra sheet or face data is demanded of a replaceable piece.
    f=Stream(p);f.extend(baseclauses);f.extend(sorted(pumped));f.to_file(str(p))
    print(label,'raw core',len(cs),'retained from unchanged blocks',len(baseclauses),'recovered by strip',recover,'omitted',omit,flush=True)
    flags={t[2]:v for v,t in ts.items() if t[0]=='s'}
    if '--all' in sys.argv:
        assert omit==0
        chkclauses=set(map(lambda c:tuple(sorted(c)),baseclauses))|pumped
        assert all(tuple(sorted(c)) in chkclauses for c in cs)
        with p.with_suffix('.log').open('wb') as o:
            rc=subprocess.run(['target/cadical/build/cadical','-t','240',str(p),str(p.with_suffix('.drat'))],stdout=o).returncode
        if rc==20:
            data=subprocess.run(['target/drat-trim/drat-trim',str(p),str(p.with_suffix('.drat'))],capture_output=True,check=True).stdout
            assert b's VERIFIED' in data;p.with_suffix('.check').write_bytes(data);print('entire strip transfer s VERIFIED')
        else:assert rc==0;print('UNKNOWN (full original UNSAT core included)')
        return
    with Solver(name='cadical195',bootstrap_with=baseclauses) as solver:
        solver.append_formula(pumped);ans={}
        for d,z in sorted(flags.items()):
            solver.conf_budget(budget);ans[d]=str(solver.solve_limited(assumptions=[z,*[-w for e,w in flags.items() if e!=d]]))
    dead=[d for d,v in ans.items() if v=='False']
    if dead:
        from itertools import combinations
        f=Stream(p);f.extend(baseclauses);f.extend(sorted(pumped))
        f.extend([[-a,-b] for a,b in combinations(flags.values(),2)])
        f.append([flags[d] for d in dead]);f.to_file(str(p))
        with p.with_suffix('.log').open('wb') as o:
            rc=subprocess.run(['target/cadical/build/cadical','-t','240',str(p),str(p.with_suffix('.drat'))],stdout=o).returncode
        if rc==20:
            data=subprocess.run(['target/drat-trim/drat-trim',str(p),str(p.with_suffix('.drat'))],capture_output=True,check=True).stdout
            assert b's VERIFIED' in data;p.with_suffix('.check').write_bytes(data)
            for d in dead:ans[d]='VERIFIED'
        else:assert rc==0
    from collections import Counter
    print(Counter(ans.values()),'excluded',[k for k,v in ans.items() if v=='VERIFIED'],flush=True)
    p.with_suffix('.json').write_text(json.dumps(ans)+'\n')
if __name__=='__main__':test(bool(int(sys.argv[1])),sys.argv[2],int(sys.argv[3]))
