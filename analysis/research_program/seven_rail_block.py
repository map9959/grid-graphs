"""Insert drifting 7-row rail bands and widen by 21, then test forest-preserving repairs."""
from pathlib import Path
from .extend_forest_23 import old,verify
from .repeat_forest_38 import duplicate


def block(rows):
    # The core of rows 11..17 moves three columns right in seven rows.
    # Shift a 3-column padding unit from right to left after each band.
    def pad(s,a):
        return s[:2]+a*s[2:5]+s[2:33]+(7-a)*s[33:36]+s[33:]
    return ([pad(s,0) for s in rows[:11]]+
            [pad(s,h) for h in range(3) for s in rows[11:18]]+
            [pad(s,3) for s in rows[11:]])


def repair(rows,box,limit=3000,gain=1):
    from pysat.solvers import Solver
    from pysat.card import CardEnc,EncType
    n=len(rows);a,b,c,d=box
    inside=[(i,j) for i in range(a,b) for j in range(c,d)]
    ids={p:k+1 for k,p in enumerate(inside)}
    oldset={(i,j) for i,s in enumerate(rows) for j,ch in enumerate(s) if ch=='#'}
    const=oldset-ids.keys();target=len(oldset)-len(const)+gain
    cnf=CardEnc.atleast(list(ids.values()),bound=target,encoding=EncType.cardnetwrk)
    # Logically implied by a single unit square cycle.
    for i,j in inside:
        for di in (-1,1):
            for dj in (-1,1):
                p=i+di,j+dj
                if p in const:cnf.append([-ids[i,j]])
                if p in ids:cnf.append([-ids[i,j],-ids[p]])
    # Contract the frozen forced forest, preserving its components.
    def root(p,x):
        while x!=p[x]:p[x]=p[p[x]];x=p[x]
        return x
    edges={}
    for u in range(n*n):
        i,j=divmod(u,n)
        for v in ([u+1] if j+1<n else [])+([u+n] if i+1<n else []):
            cells=((i,j),divmod(v,n))
            if any(t in const for t in cells):edges[u,v]=()
            elif any(t in ids for t in cells):edges[u,v]=tuple(ids[t] for t in cells if t in ids)
    par=list(range(n*n))
    for (u,v),ls in edges.items():
        if not ls:
            x,y=root(par,u),root(par,v);assert x!=y;par[x]=y
    dynamic=[(root(par,u),root(par,v),ls) for (u,v),ls in edges.items() if ls]
    with Solver(name='cadical195',bootstrap_with=cnf) as s:
        s.set_phases([t if p in oldset else -t for p,t in ids.items()])
        for _ in range(limit):
            s.conf_budget(8000)
            if s.solve_limited() is not True:return None
            sol=set(s.get_model());p=list(range(n*n));adj={};excluded=False
            for u,v,ls in dynamic:
                mark=next((t for t in ls if t in sol),None)
                if mark is None:continue
                x,y=root(p,u),root(p,v)
                if x!=y:
                    p[x]=y;adj.setdefault(u,[]).append((v,mark));adj.setdefault(v,[]).append((u,mark));continue
                prev={u:None};q=[u]
                while v not in prev:
                    z=q.pop()
                    for w,t in adj[z]:
                        if w not in prev:prev[w]=(z,t);q.append(w)
                neg={-mark};w=v
                while w!=u:w,t=prev[w];neg.add(-t)
                s.add_clause(list(neg));excluded=True
            if not excluded:
                marked=const|{k for k,t in ids.items() if t in sol}
                out=[''.join('#' if (i,j) in marked else '.' for j in range(n)) for i in range(n)]
                assert verify(out)[0]>=len(oldset)+gain
                return out


if __name__=='__main__':
    import sys
    r=old(38)
    r=duplicate(r,14,4) if '--41' in sys.argv else block(r)
    print('starting forest',len(r),verify(r),flush=True)
    if '--repair' in sys.argv:
        n=len(r)
        for h,w in ((6,10),(10,10),(8,16)):
            for i in sorted(set(range(0,n-h+1,4))|{n-h}):
                for j in sorted(set(range(0,n-w+1,5))|{n-w}):
                    t=repair(r,(i,i+h,j,j+w),limit=400)
                    if t:
                        r=t;print('repair',i,j,verify(r),flush=True)
                        Path(__file__).with_name(f'block_repair_{n}.txt').write_text('\n'.join(r)+'\n')
                        if verify(r)[0]>={41:597,59:1214}[n]:sys.exit()
