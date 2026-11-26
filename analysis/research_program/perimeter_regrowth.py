"""Search a replacement annulus around the independent roots of a one-gap crop.

Frozen straight middles can be stretched. A successful model must replay as
a physical forest, including the two NW ports joined through the old tooth.
"""
from collections import defaultdict,deque
from itertools import product
from pathlib import Path
import sys

def search(n,q,a,b,r):
    from pysat.formula import CNF,IDPool
    from pysat.card import CardEnc
    from pysat.solvers import Solver
    N=n+3*q;k=(n-2)//3
    assert n%42==35 and 0<=a<=3*q and 0<=b<=3*q
    lo,hi=a+1,a+n-2;le,ri=b+1,b+n-2
    ann={(i,j) for i,j in product(range(N),repeat=2) if not(lo<=i<=hi and le<=j<=ri)}
    U=lambda k:3*k*k+7*k-(k-5)//7
    probe='--equal' in sys.argv
    goal=4*n-9+U(k+q)-U(k)+int(not probe)
    fixed=set();free=set();tooth=(a+2,b+2)
    for i,j in ann:
        if le+r<=j<=ri-r:
            z=i if i<lo else N-1-i
        elif lo+r<=i<=hi-r:
            z=j if j<le else N-1-j
        else:free.add((i,j));continue
        if z%3==0:fixed.add((i,j))
    vp=IDPool();X={p:vp.id(p) for p in sorted(free)};f=CNF()
    base=fixed|{tooth}
    def ban(points):
        c=[-X[p] for p in points if p in X];f.append(c);return c
    for i,j in free|base:
        for d in (1,-1):
            y=(i+1,j+d)
            if y in free|base:ban(((i,j),y))
    f.extend(CardEnc.atleast(lits=list(X.values()),bound=goal-len(fixed),vpool=vp,encoding=2).clauses)
    # Restrict a known necessary forest condition by contracting the
    # fixed straight sides. Enumerate all cycles in the candidate graph,
    # then require that some marked owner of each cycle disappear.
    def cuts(M):
        es=set();par={};adj=defaultdict(list)
        for i,j in M:
            for u,v in ((i-1,j),(i+1,j),(i,j+1),(i,j-1)):
                if 0<=u<N and 0<=v<N:es.add(tuple(sorted(((i,j),(u,v)))))
        def rt(x):
            while x in par:x=par[x]
            return x
        for x,y in sorted(es):
            u,v=rt(x),rt(y)
            if u!=v:par[u]=v;adj[x].append(y);adj[y].append(x);continue
            prev={x:None};todo=deque([x])
            while y not in prev:
                s=todo.popleft()
                for t in adj[s]:
                    if t not in prev:prev[t]=s;todo.append(t)
            cycle=[(x,y)]
            while y!=x:cycle.append((prev[y],y));y=prev[y]
            owners=set()
            for s,t in cycle:
                if s in base or t in base:continue
                if s not in owners and t not in owners:owners.add(s if s in M else t)
            yield owners
    print('annulus side',n,'growth',3*q,'shift',a,b,'free marks',len(free),'target',goal,'fixed',len(fixed),flush=True)
    cap=next((int(s[6:]) for s in sys.argv if s.startswith('--cap=')),2000)
    with Solver(name='cadical195',bootstrap_with=f.clauses) as solver:
        for it in range(cap):
            if not solver.solve():print('annular ansatz UNSAT (not a board exclusion)',it);return
            A=set(solver.get_model());M=base|{p for p,v in X.items() if v in A}
            bad=list(cuts(M))
            if not bad:
                assert len(M)-1>=goal
                if probe:
                    from .annular_debit import price
                    from .defect_window import table
                    if it==0 or 'tab' not in locals():tab=table(N)
                    star=next((int(s[7:]) for s in sys.argv if s.startswith('--star=')),None)
                    debit,roots=price(n,N,a,b,ann,M-{tooth},tab,star)
                    if debit<=936:
                        solver.add_clause([-X[p] for p in M if p in X])
                        if 'best_debit' not in locals() or debit>best_debit:
                            best_debit=debit;print('equality annulus debit (without isolate)',debit,'corner sinks',roots,flush=True)
                        continue
                print('verified annular replacement',len(M)-1,'required',goal,'iteration',it)
                Path(f'target/regrowth_{n}_{q}_{a}_{b}_{r}.txt').write_text(''.join(''.join('#' if (i,j) in M-{tooth} else '.' for j in range(N))+'\n' for i in range(N)))
                return
            for c in bad:solver.add_clause(ban(c))
    print('unresolved at cut limit',cap)
if __name__=='__main__':search(*map(int,sys.argv[1:6]))
