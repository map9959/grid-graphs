"""Generate necessary 4x4 projection cuts on the fine diagonal-sector chart."""
from collections import defaultdict,Counter
from itertools import product
from functools import lru_cache
from .diagonal_chart import relaxation,count,Q,Path,json
from .side28_score import solve
from .four_square import masks4
from .patch_square import trans,SYM,MASKS
from .sector_fine_seams import lift
import sys

def contexts(n,ns,d,w):
    s=n-2;h=d+3
    def pt(i,j):
        ax=lambda u:u if u<h else 2*h+3+u-s if u>=s-h else h+(u-h)%3
        clip=lambda u:max(-w-5,min(w+5,u))
        return ax(i),ax(j),clip(i-j),clip(i+j+1-s)
    loc={ij:pt(*ij) for ij in product(range(s),repeat=2)}
    imgs={p:[loc[trans(*ij,s,g)] for g in range(8)] for ij,p in loc.items()}
    names={p:{m:ns['p',min(zip(ps,SYM[m]))] for m in MASKS} for p,ps in imgs.items()}
    groups=defaultdict(set)
    for (i,j),p in loc.items():
        for off,(dx,dy) in enumerate(product(range(2),repeat=2)):
            groups[p,off].add(tuple(loc.get((i+a-dx,j+b-dy)) for a,b in product(range(2),repeat=2)))
    return [(off,tuple(names[p] for p in cs)) for (p,off),ss in groups.items() if len(ss)==1
            for cs in ss if None not in cs]

def separate(groups,X):
    words=sorted({ls for ls,_ in masks4().values()});possible=defaultdict(list)
    for ls in words:
        for t,z in enumerate(ls):possible[t,z].append(ls)
    rows=set()
    for t,p in groups:
        live=[{m for m,x in q.items() if X[x]>1e-8} for q in p]
        for m in live[t]:
            opts=possible[t,m];sets=[]
            for ls in opts:
                out=tuple((j,z) for j,z in enumerate(ls) if j!=t and z not in live[j])
                if not out:break
                sets.append(out)
            else:
                hits=[]
                while sets:
                    counts=Counter(u for o in sets for u in o)
                    h=max(counts,key=counts.get);hits.append(h);sets=[o for o in sets if h not in o]
                c=Counter({p[t][m]:1})
                for j,z in hits:c[p[j][z]]-=1
                rows.add(tuple(sorted((v,a) for v,a in c.items() if a)))
    return sorted(rows)

def run(base,n,d,w,rounds):
    ns,rr,obj=relaxation(base,d+4,pooled=d,period=3,diagonal=w)
    inv={x:k for k,x in ns.items()};A=[];rhs=[];norm={}
    for row,op,b in rr:
        if op=='=' and b>0:
            kind,atom=inv[row[0][0]];p=int(kind=='p');b,_,_=count(n-2*p,d+4-p,w+5,atom[0])
            norm[len(A)]=(p,atom[0])
        A.append((row,op));rhs.append(b)
    more=lift(base,ns,d,w);A.extend(more);rhs.extend([0]*len(more))
    groups=contexts(base,ns,d,w);seen=set()
    for it in range(rounds+1):
        z,y,X=solve(A,rhs,obj,ns,interior=False);k=(n-1)//3
        vals=[sum(y[i]*count(n-2*p,d+4-p,w+5,pt)[j] for i,(p,pt) in norm.items()) for j in (1,2)]
        print('round',it,'extra cuts',len(seen),'excess over comb',z-3*k*k-5*k-(3*k-13)//10,
              '+6 difference vs old upper',vals[0]-(12*k+12+32/3),'curvature vs 24',vals[1]-24,flush=True)
        if it==rounds:break
        cuts=set(separate(groups,X))-seen
        if not cuts:break
        seen.update(cuts);A.extend((c,'<=') for c in sorted(cuts));rhs.extend([0]*len(cuts))
if __name__=='__main__':run(*map(int,sys.argv[1:]))
