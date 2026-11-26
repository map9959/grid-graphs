"""A pooled law on every 4-by-4 forest patch, coupled to all four 3-by-3 marginals."""
from .repeating_patch_dual import polynomial,Q
from .patch_square import trans,SYM,MASKS,Counter
from functools import lru_cache
from itertools import product
from collections import defaultdict

@lru_cache(None)
def masks4():
    out={}
    for c in product(range(16),repeat=4):
        if any(a&((b<<1)|(b>>1)) for a,b in zip(c,c[1:])):continue
        m=sum(v<<(4*i) for i,v in enumerate(c));p=list(range(16))
        def root(x):
            while p[x]!=x:x=p[x]
            return x
        good=True
        for i in range(16):
            for j in ([i+1] if i%4<3 else [])+([i+4] if i<12 else []):
                if (m>>i|m>>j)&1:
                    a,b=root(i),root(j)
                    if a==b:good=False;break
                    p[a]=b
            if not good:break
        if not good:continue
        sub=tuple(sum(((m>>(4*(i+a)+j+b))&1)<<(3*a+b) for a,b in product(range(3),repeat=2)) for i,j in product(range(2),repeat=2))
        assert all(v in MASKS for v in sub)
        imgs=tuple(sum(1<<(4*r+c) for i,j in product(range(4),repeat=2) if m>>(4*i+j)&1 for r,c in [trans(i,j,4,g)]) for g in range(8))
        out[m]=sub,imgs
    return out

def lift(n,ns,depth,period,cd,diagonal=None):
    S=n-3
    def ax(i,S,d):return i if i<d else 2*d+period+i-S if i>=S-d else d+(i-d)%period
    def pos(i,j,T,d):
        w=(diagonal or 0)+(5 if T!=S else 0)
        return tuple((ax(a,T,d),ax(b,T,d))+(tuple(max(-w,min(w,z)) for z in (a-b,a+b+1-T)) if diagonal is not None else ()) for g in range(8) for a,b in [trans(i,j,T,g)])
    reps={};child=defaultdict(dict)
    for i,j in product(range(S),repeat=2):
        p=pos(i,j,S,cd);reps[p[0]]=p
        for s,(di,dj) in enumerate(product(range(2),repeat=2)):
            k=pos(i+di,j+dj,S+1,depth)
            child[p[0],s][k[0]]=k
    maps={};seen=set();A=[];weights=masks4()
    for k,p in sorted(reps.items()):
        groups=[defaultdict(Counter) for _ in range(4)]
        for m,(sub,imgs) in weights.items():
            atom=('q',min(zip(p,imgs)));x=ns.setdefault(atom,'q'+str(len(ns)))
            for s,v in enumerate(sub):groups[s][v][x]+=1
        for s in range(4):
            for v in MASKS:
                cs=groups[s][v].copy()
                for pt in child[k,s].values():cs[ns['p',min(zip(pt,SYM[v]))]]-=1
                row=tuple(sorted(cs.items()))
                if row not in seen:seen.add(row);A.append((row,'='))
    return A

def run():
    import sys
    from .side28_score import solve
    d=int(sys.argv[1]);cd=int(sys.argv[2]);n=int(sys.argv[3])
    n0,ns,A,b,obj=polynomial(d,3,1);R=lift(n0,ns,d+3,3,cd);A+=R;b+=[(0,0,0)]*len(R)
    j=(n-n0)//3;rhs=[a+j*v+j*(j-1)//2*e for a,v,e in b]
    print('mask count',len(masks4()),'typed variables',len(ns),'rows',len(A),flush=True)
    val,y,sol=solve(A,rhs,obj,ns,interior=True)
    print('side',n,'pooled 4x4 LP',val,'Newton triples',[sum(v*c[i] for v,c in zip(y,b)) for i in range(3)],flush=True)
if __name__=='__main__':run()
