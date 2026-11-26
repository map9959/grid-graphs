"""Collect physical cycle cuts; emit a fixed CNF for independent DRAT checking."""
from .side28_sat import cnf,cycle
from .patch_square import Path,json,trans
import sys


def run(generate):
    from pysat.solvers import Solver
    n=35
    sys.setrecursionlimit(3000)
    f,sites=cnf(n,scale=168)
    path=Path(__file__).with_name('side35_cycles.json')
    def cuts(w):
        # w traverses distinct grid vertices in cyclic order. The specified
        # subset of marked vertices covers every edge of this closed path.
        p,m=w
        assert len(p)>=4 and len(set(p))==len(p) and set(m)<=set(p)
        for a,b in zip(p,p[1:]+p[:1]):
            assert 0<=a<n*n and abs(a//n-b//n)+abs(a%n-b%n)==1 and (a in m or b in m)
        return sorted({tuple(sorted(-sites[n*i+j] for u in m for i,j in [trans(*divmod(u,n),n,g)])) for g in range(8)})
    if generate:
        ws=[]
        with Solver(name='cadical195',bootstrap_with=f) as s:
            while s.solve():
                yy=set(s.get_model());v={i for i,x in enumerate(sites) if x in yy}
                p=cycle(v,n)
                assert p is not None,'found a forest at score 440'
                m=set(p)&v
                for i,a in enumerate(p):
                    if p[i-1] in m and p[(i+1)%len(p)] in m:m.discard(a)
                w=[p,sorted(m)];ws.append(w)
                for c in cuts(w):s.add_clause(c)
        path.write_text(json.dumps(ws,separators=(',',':'))+'\n')
    ws=json.loads(path.read_text())
    for w in ws:f.extend(cuts(w))
    f.to_file('target/forest35.cnf')
    print('verified cycle generators',len(ws),'physical CNF variables',f.nv,'clauses',len(f.clauses),flush=True)


if __name__=='__main__':run('--generate' in sys.argv)
