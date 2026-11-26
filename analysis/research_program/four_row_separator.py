"""Support separation of physical four-row forest distributions."""
from functools import lru_cache
from itertools import product
from .tied_cap_primal import model,Q,Path,json
from .patch_square import MASKS,SYM,trans


def probabilities(n):
    ns,_,_=model(8,n)
    y={x:Q(v) for x,v in json.loads(Path(__file__).with_name('tied_cap_obstruction_r1.json').read_text()).items()}
    def ax(i):return i if i<7 else 17-(n-2)+i if i>=n-9 else 7+(i-7)%3
    @lru_cache(None)
    def prob(i,j):
        pos=[tuple(map(ax,trans(i,j,n-2,g))) for g in range(8)]
        return {m:q for m in MASKS if (q:=y.get(ns['p',min(zip(pos,SYM[m]))],0))}
    return prob


@lru_cache(None)
def masks(a,b,c):
    m=sum(((x>>r)&1)<<(3*r+i) for i,x in enumerate((a,b,c)) for r in range(4))
    return m&511,m>>3


@lru_cache(None)
def forest(cols):
    w=len(cols);p=list(range(4*w))
    def root(u):
        while p[u]!=u:u=p[u]
        return u
    for j,x in enumerate(cols):
        for r in range(4):
            for v,on in ((4*j+r+1,r<3 and (x|(x>>1))>>r&1),
                         (4*j+r-4,j>0 and (x|cols[j-1])>>r&1)):
                if on:
                    a,b=root(4*j+r),root(v)
                    if a==b:return False
                    p[a]=b
    return True


def scan(n=109):
    prob=probabilities(n)
    for width in range(3,11):
        for i,j in product(range(12),repeat=2):
            words=[(a,b) for a,b in product(range(16),repeat=2)]
            for t in range(width-2):
                top,bot=prob(i,j+t),prob(i+1,j+t)
                words=[v+(c,) for v in words for c in range(16) if
                       (m:=masks(*v[-2:],c))[0] in top and m[1] in bot and forest(v+(c,))]
            for t,r in product(range(width-2),range(2)):
                good={masks(*v[t:t+3])[r] for v in words}
                for m,q in prob(i+r,j+t).items():
                    if m not in good:
                        print('impossible support',i,j,width,t,r,m,q,'compatible words',len(words));return i,j,width,t,r,m


def separate(n=109):
    import highspy as H
    prob=probabilities(n)
    for width in range(3,15):
        for i,j in product(range(11),repeat=2):
            words=[(a,b) for a,b in product(range(16),repeat=2)]
            for t in range(width-2):
                top,bot=prob(i,j+t),prob(i+1,j+t)
                words=[v+(c,) for v in words for c in range(16) if
                       (m:=masks(*v[-2:],c))[0] in top and m[1] in bot and forest(v+(c,))]
            cols=[[(t,r,m) for t in range(width-2) for r,m in enumerate(masks(*v[t:t+3]))] for v in words]
            events=[(t,r,m) for t,r in product(range(width-2),range(2)) for m in sorted(prob(i+r,j+t))]
            # Maximize feasible subdistribution mass, bounded by the prescribed marginals.
            h=H.Highs();h.setOptionValue('output_flag',False);h.setOptionValue('threads',1)
            N=len(words);h.addVars(N,[0.]*N,[H.kHighsInf]*N);h.changeColsCost(N,list(range(N)),[1.]*N)
            for t,r,m in events:
                idx=[s for s,col in enumerate(cols) if (t,r,m) in col]
                h.addRow(-H.kHighsInf,float(prob(i+r,j+t)[m]),len(idx),idx,[1.]*len(idx))
            h.setMaximize();h.run()
            if h.getObjectiveValue()<.999999:
                y={k:Q(float(v)).limit_denominator(10000) for k,v in zip(events,h.getSolution().row_dual) if abs(v)>1e-8}
                assert min(y.values())>=0 and all(sum(y.get(k,0) for k in col)>=1 for col in cols)
                lhs=sum(v*prob(i+r,j+t)[m] for (t,r,m),v in y.items());assert lhs<1
                print('separated',i,j,width,'left',lhs,'<1',y,flush=True)
                return i,j,width,y
        print('passed width',width,flush=True)


@lru_cache(None)
def advance(state,c):
    a,b,part=state
    p=list(part)+list(range(4,8))
    def root(u):
        while p[u]!=u:u=p[u]
        return u
    for u,v,on in [(r,r+4,(b|c)>>r&1) for r in range(4)]+[(4+r,5+r,(c|c>>1)>>r&1) for r in range(3)]:
        if on:
            x,y=root(u),root(v)
            if x==y:return None
            p[x]=y
    roots=[root(i) for i in range(4,8)]
    return b,c,tuple(roots.index(v) for v in roots)


def flow(n=109):
    from collections import defaultdict
    import highspy as H
    prob=probabilities(n)
    for i in range((n-2)//2+1):
        states={(0,0,tuple(range(4)))};rows=defaultdict(list);b={};N=0
        for j in range(n):
            nextstates=set()
            for s in sorted(states):
                for c in range(16):
                    ev=masks(s[0],s[1],c)
                    if j>=2 and any(m not in prob(i+r,j-2) for r,m in enumerate(ev)):continue
                    d=advance(s,c)
                    if d is None:continue
                    k=('flow',j,s);rows[k].append((N,1));b[k]=Q(int(j==0))
                    if j+1<n:
                        k=('flow',j+1,d);rows[k].append((N,-1));b[k]=Q(0)
                    if j>=2:
                        for r,m in enumerate(ev):
                            k=('patch',j-2,r,m);rows[k].append((N,1));b[k]=prob(i+r,j-2)[m]
                    N+=1;nextstates.add(d)
            states=nextstates
        for j,r in product(range(n-2),range(2)):
            for m,q in prob(i+r,j).items():b['patch',j,r,m]=q
        h=H.Highs();h.setOptionValue('output_flag',False);h.setOptionValue('threads',1)
        h.addVars(N,[0.]*N,[H.kHighsInf]*N)
        for k,q in b.items():
            row=rows[k];h.addRow(float(q),float(q),len(row),[v for v,w in row],[w for v,w in row])
        h.run()
        if h.getModelStatus()!=H.HighsModelStatus.kOptimal:
            print('NOT feasible strip',i,h.getModelStatus(),flush=True);return
        y=[Q(float(v)).limit_denominator(1000000) for v in h.getSolution().col_value]
        assert min(y)>=0 and all(sum(y[v]*w for v,w in rows[k])==q for k,q in b.items())
        print('exact strip',i,'arcs',N,flush=True)
        if i>=10:break # remaining rows have periodic bulk types or their reflections


if __name__=='__main__':
    import sys
    if '--flow' in sys.argv:flow()
    elif '--lp' in sys.argv:separate()
    else:scan()
