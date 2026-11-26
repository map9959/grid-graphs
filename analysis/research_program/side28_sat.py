"""Physical SAT with lazy forced-cycle clauses and exact dual gap pruning."""
from .patch_square import relaxation,SYM,trans,MASKS,DIR,Q,Path,json,Counter,signature
from .side28_integer import counts
from itertools import product


def cnf(n=28,scale=24,target=None,stencil=False):
    if target is None:target={23:196,26:248,28:289,29:306,32:370,34:420,35:440,38:515,40:575,41:597}[n]
    from pysat.formula import IDPool,CNF
    from pysat.card import CardEnc,EncType
    from pysat.pb import PBEnc
    from .square_current import states
    if stencil:
        from .square_dual_physical import inspect
        base,slacks=inspect(n,physical_costs=True)
        weights={k:int(scale*v) for k,v in slacks.items()}
    else:
        ns,rows,obj=relaxation(n)
        cert=json.loads(Path(__file__).with_name(f'patch_square_{n}_dual.json').read_text())
        assert cert['model']==signature(rows,obj)
        dual={i:Q(y) for i,y in cert['multipliers']}
        res=Counter(obj);base=Q(0)
        for i,(row,op,b) in enumerate(rows):
            q=dual.get(i,0)
            assert op=='=' or (q<=0 if op=='>=' else q>=0)
            base+=q*b
            for x,w in row:res[x]-=w*q
        base+=sum(max(v,0) for v in res.values())
        mult=counts(ns,n);weights={k:max(0,int(-scale*res[x]/mult[x])) for k,x in ns.items()}
    budget=int(scale*(base-target));pool=IDPool();f=CNF()
    sites=[pool.id(('v',u)) for u in range(n*n)];weighted={}
    def weight(key,w,guards):
        if w>budget:f.append([-z for z in guards])
        elif w:
            v=pool.id(key);weighted[v]=w
            f.append([v]+[-z for z in guards])
    for i,j in product(range(n),repeat=2):
        u=i*n+j
        dirs=[d for d,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n]
        og={d:pool.id(('arrow',u,d)) for d in dirs}
        for d in dirs:
            for e in dirs:
                if e>d:f.append([-og[e],-og[d]])
        if u==0:
            for a in og.values():f.append([-a])
        for d in dirs:
            a,b=DIR[d];v=(i+a)*n+j+b
            if d<2:
                back=pool.id(('arrow',v,d+2))
                f.extend([[-og[d],-back],[-sites[u],og[d],back],[-sites[v],og[d],back],
                          [-og[d],sites[u],sites[v]],[-back,sites[u],sites[v]]])
        pos=[trans(i,j,n,g) for g in range(8)]
        for bit,sig in states(dirs):
            out=next((d for d,e in sig.items() if e[2]==(1 if d<2 else -1)),-1)
            nb=[sig[d][1 if d<2 else 0] if d in dirs else 9 for d in range(4)]
            ims=[]
            for g,p in enumerate(pos):
                word=[9]*4
                def turn(d):return ((2-d if g&4 else d)+g%4)%4
                for d in dirs:word[turn(d)]=nb[d]
                ims.append((p,bit,tuple(word),turn(out) if out>=0 else -1))
            w=weights['s',min(ims)]
            if not w:continue
            guard=[sites[u] if bit else -sites[u]]
            for d in dirs:
                a,b=DIR[d];z=sites[(i+a)*n+j+b];guard.append(z if nb[d] else -z)
            guard+=([og[out]] if out>=0 else [-a for a in og.values()])
            weight(('s',u,w),w,guard)
    for i,j in product(range(n-2),repeat=2):
        pos=[trans(i,j,n-2,g) for g in range(8)]
        vv=[sites[(i+r)*n+j+c] for r,c in product(range(3),repeat=2)]
        # A prefix trie over masks enforces legal domains and relates the
        # whole pattern to its cost without listing all 412 forbidden masks.
        labels=[]
        for m in MASKS:
            w=weights['p',min(zip(pos,SYM[m]))]
            if w>budget:continue
            z=pool.id(('mask',i,j,m));labels.append(z)
            for b,t in enumerate(vv):f.append([-z,t if m>>b&1 else -t])
            if w:weight(('p',i,j,w),w,[z])
        f.append(labels)
    f.extend(CardEnc.atleast(sites,bound=target,vpool=pool,encoding=EncType.cardnetwrk).clauses)
    f.extend(PBEnc.atmost(lits=list(weighted),weights=list(weighted.values()),bound=budget,vpool=pool,encoding=8).clauses)
    return f,sites


def cycle(selected,n):
    adj=[[] for _ in range(n*n)]
    for u in range(n*n):
        for v in ([u+1] if u%n<n-1 else [])+([u+n] if u+n<n*n else []):
            if u in selected or v in selected:adj[u].append(v);adj[v].append(u)
    seen=set();parent={}
    def dfs(u,p):
        seen.add(u);parent[u]=p
        for v in adj[u]:
            if v==p:continue
            if v in seen:
                path=[u]
                while path[-1]!=v:path.append(parent[path[-1]])
                return path
            path=dfs(v,u)
            if path:return path
    for u in range(n*n):
        if u not in seen:
            path=dfs(u,-1)
            if path:return path


if __name__=='__main__':
    from pysat.solvers import Solver
    import sys
    n=23 if '--23' in sys.argv else 40 if '--40' in sys.argv else 34 if '--34' in sys.argv else 28
    sys.setrecursionlimit(max(sys.getrecursionlimit(),n*n+20))
    f,sites=cnf(n)
    with Solver(name='cadical195',bootstrap_with=f) as s:
        print('physical SAT',f.nv,'variables,',len(f.clauses),'clauses',flush=True)
        while s.solve():
            sol=set(s.get_model());sel={i for i,t in enumerate(sites) if t in sol}
            path=cycle(sel,n)
            if not path:
                assert len(sel)>={23:196,28:289,34:420,40:575}[n]
                print('verified forest',sorted(sel));break
            s.add_clause([-sites[u] for u in path if u in sel])
        else:print('UNSAT (requires certificate)')
