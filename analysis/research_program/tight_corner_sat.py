"""Necessary conditions at the 1/14 gap, with independent rootings at four corners."""
from itertools import product,combinations
from functools import lru_cache
from .square_dual_physical import inspect,trans,SYM,DIR,MASKS
from pathlib import Path


@lru_cache(None)
def cover(values):
    """Cover a Boolean predicate by subcubes; check coverage and soundness."""
    n=(len(values)-1).bit_length();full=(1<<n)-1
    yes={a for a,b in enumerate(values) if b}
    cubes=[];left=set(yes)
    for k in range(n+1):
        if not left:break
        for ds in combinations(range(n),k):
            m=sum(1<<d for d in ds)
            for v in sorted({a&m for a in left}):
                if not any(a&m==v for a in left):continue
                s=full^m
                while (s|v) in yes and s:s=(s-1)&(full^m)
                if (s|v) not in yes:continue
                cubes.append((m,v));left={a for a in left if a&m!=v}
    assert all(bool(b)==any(a&m==v for m,v in cubes) for a,b in enumerate(values))
    return cubes


def generate(n=77,depth=None,rootings=4,turns=False,planar=False,matching=False,single=False):
    from pysat.formula import IDPool,CNF
    from pysat.pb import PBEnc
    assert n>=35 and (n-35)%21==0
    if single:assert (n-35)%42==0
    k=(n-2)//3
    target=3*k*k+7*k+(23-2*k)//14
    u,slacks=inspect(n,physical_costs=True);scale=1008;budget=int((u-target)*scale)
    assert budget==72
    cheapest=min(q for (t,k),q in slacks.items() if t=='s' and k[0]!=(0,0) and k[1] and k[-1]==-1)
    corner_leaf=slacks['s',((0,0),0,(0,1,9,9),-1)]
    assert cheapest>u-target and corner_leaf>u-target
    print('noncorner marked sink >=',cheapest,'unmarked one-neighbor corner sink',corner_leaf,flush=True)
    pool=IDPool();f=CNF();bits=[pool.id(('v',i)) for i in range(n*n)]
    corners=[0,n-1,n*n-1,n*n-n]
    shared={}
    def charge(table,vs,guard,bank):
        if single:table=[q if q in (0,72) else budget+1 for q in table]
        levels=sorted(set(w for w in table if 0<w<=budget))
        for ds,v in cover(tuple(w>budget for w in table)):
            f.append(guard+[(-x if (v>>d)&1 else x) for d,x in enumerate(vs) if ds>>d&1])
        prev=0
        for w in levels:
            ind=pool.id();bank[ind]=w-prev;prev=w
            for ds,v in cover(tuple(x>=w for x in table)):
                f.append(guard+[ind]+[(-x if (v>>d)&1 else x) for d,x in enumerate(vs) if ds>>d&1])
    for i,j in product(range(n-2),repeat=2):
        if depth is not None and min(i,j,n-3-i,n-3-j)>=depth:continue
        pos=[trans(i,j,n-2,g) for g in range(8)]
        tab=[budget+1]*512
        for m in MASKS:tab[m]=int(scale*slacks['p',min(zip(pos,SYM[m]))])
        charge(tab,[bits[(i+a)*n+j+b] for a,b in product(range(3),repeat=2)],[],shared)
    # All four corners must belong to one component: two corner sinks
    # would cost 9/14, more than the available gap. An unmarked corner
    # is either isolated, adjacent to one mark (root cost 3/28), or has
    # both neighbors marked (forced square). None can occur.
    for x in corners:f.append([bits[x]])
    # Forbid two fully forced rungs joined by fully forced rails on
    # both sides. The state only propagates while the rails continue.
    edge={}
    def forced(a,b):
        k=tuple(sorted((a,b)))
        if k not in edge:
            x=pool.id();edge[k]=x
            f.extend([[-bits[a],x],[-bits[b],x],[-x,bits[a],bits[b]]])
        return edge[k]
    for height in (2,3,4):
        for swap in (False,True):
            for i in range(n-height):
                if depth is not None and min(i,n-1-height-i)>depth:continue
                state=None
                for j in range(n):
                    site=lambda r,c:n*c+r if swap else n*r+c
                    rung=[forced(site(r,j),site(r+1,j)) for r in range(i,i+height)]
                    nxt=pool.id()
                    f.append([nxt]+[-x for x in rung])
                    if state is not None:
                        cond=[-state,-forced(site(i,j-1),site(i,j)),-forced(site(i+height,j-1),site(i+height,j))]
                        f.append(cond+[nxt]);f.append(cond+[-x for x in rung])
                    state=nxt
    for ri,root in enumerate(corners[:rootings]):
        bank=shared.copy()
        for i,j in product(range(n),repeat=2):
            if depth is not None and min(i,j,n-1-i,n-1-j)>=depth+1:continue
            u=i*n+j
            dirs=[d for d,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n]
            vv=[(i+DIR[d][0])*n+j+DIR[d][1] for d in dirs]
            og=[pool.id((ri,u,d)) for d in dirs]
            for a,b in combinations(og,2):f.append([-a,-b])
            if u==root:
                for a in og:f.append([-a])
            elif u in corners:f.append(og)
            else:
                # A component outside the corners that has a forced edge
                # contains a mark. Root it at the mark: that sink alone
                # costs more than the budget. Thus only isolates may be
                # sinks outside the chosen corner in a feasible forest.
                for v in [u]+vv:f.append([-bits[v]]+og)
            for h,d in enumerate(dirs):
                v=vv[h];a=og[h];back=pool.id((ri,v,(d+2)%4))
                if u<v or depth is not None:
                    f.extend([[-a,-back],[-bits[u],a,back],[-bits[v],a,back],[-a,bits[u],bits[v]],[-back,bits[u],bits[v]]])
                if turns and ri==0:
                    # Lift the four compass directions to two turns of a
                    # compass. The sheet changes exactly across the 3/0 cut.
                    # A path in a rooted forest always admits such labels.
                    # A directed simple grid cycle would wind once, changing
                    # sheet and returning to its starting edge: impossible.
                    xu=pool.id(('sheet',u));xv=pool.id(('sheet',v))
                    for e,(di,dj) in enumerate(DIR):
                        if e==(d+2)%4 or not (0<=v//n+di<n and 0<=v%n+dj<n):continue
                        g=[-a,-pool.id((ri,v,e))]
                        lit=-xv if abs(e-d)==3 else xv
                        f.extend([g+[-xu,lit],g+[xu,-lit]])
            pos=[trans(i,j,n,g) for g in range(8)]
            for out in [-1]+dirs:
                guard=og[:] if out<0 else [-og[dirs.index(out)]]
                tab=[]
                for m in range(1<<(1+len(dirs))):
                    b=m&1;ls=[9]*4
                    for h,d in enumerate(dirs):ls[d]=m>>(h+1)&1
                    if any(ls[d]==ls[(d+1)%4]==1 for d in range(4)) or (out>=0 and not(b or ls[out])):
                        tab.append(budget+1);continue
                    images=[]
                    for g,p in enumerate(pos):
                        rot=lambda d:((2-d if g&4 else d)+g%4)%4
                        bb=[9]*4
                        for d in dirs:bb[rot(d)]=ls[d]
                        images.append((p,b,tuple(bb),-1 if out<0 else rot(out)))
                    tab.append(int(scale*slacks['s',min(images)]))
                charge(tab,[bits[u]]+[bits[v] for v in vv],guard,bank)
        f.extend(PBEnc.atmost(lits=list(bank),weights=list(bank.values()),bound=budget,vpool=pool,encoding=8).clauses)
    if planar:
        assert rootings==4
        for i,j in product(range(n),repeat=2):
            if depth is not None and min(i,j,n-1-i,n-1-j)>=depth+1:continue
            u=n*i+j
            for d,(di,dj) in enumerate(DIR):
                if not (0<=i+di<n and 0<=j+dj<n):continue
                a,b,c,e=[pool.id((ri,u,d)) for ri in range(4)]
                # Removing a tree edge cannot split the four boundary
                # corners into alternating pairs, by planar separation.
                f.extend([[-a,b,-c,e],[a,-b,c,-e]])
    if matching:
        # Temperley primal/dual edge matching with NW primal root,
        # exterior dual root. Extend a forced forest to a spanning tree,
        # orient toward NW; its complementary dual tree orients outward.
        assert depth is None
        def one(vs):
            f.append(vs)
            for a,b in combinations(vs,2):f.append([-a,-b])
        uses={}
        def register(u,v,x):uses.setdefault(tuple(sorted((u,v))),[]).append(x)
        for i,j in product(range(n),repeat=2):
            u=n*i+j
            if u==0:continue
            choices=[]
            for d,(di,dj) in enumerate(DIR):
                if not (0<=i+di<n and 0<=j+dj<n):continue
                v=n*(i+di)+j+dj
                x=pool.id();choices.append(x);register(u,v,x)
                f.append([-pool.id((0,u,d)),x])
            one(choices)
        for i,j in product(range(n-1),repeat=2):
            u=n*i+j
            choices=[]
            for a,b in ((u,u+1),(u,u+n),(u+1,u+n+1),(u+n,u+n+1)):
                x=pool.id();choices.append(x);register(a,b,x)
                f.extend([[-x,-bits[a]],[-x,-bits[b]]])
            one(choices)
        for vs in uses.values():one(vs)
    return f,bits


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--depth',type=int);p.add_argument('--roots',type=int,default=4);p.add_argument('--out',default='target/corners77.cnf')
    p.add_argument('--turns',action='store_true')
    p.add_argument('--planar',action='store_true')
    p.add_argument('--matching',action='store_true')
    p.add_argument('--side',type=int,default=77)
    p.add_argument('--require-score',type=int)
    p.add_argument('--free-rail-margin',type=int,help='fix all marks and holes outside the free boundary strip to the default rail construction')
    p.add_argument('--single-defect',action='store_true',help='apply the odd-tail uniform charge-profile and parity exclusions')
    args=p.parse_args();f,bits=generate(n=args.side,depth=args.depth,rootings=args.roots,turns=args.turns,planar=args.planar,matching=args.matching,single=args.single_defect)
    if args.require_score is not None:
        from pysat.card import CardEnc,EncType
        f.extend(CardEnc.atleast(bits,bound=args.require_score,top_id=f.nv,encoding=EncType.cardnetwrk).clauses)
    if args.free_rail_margin is not None:
        from .zipper_rails import build
        n=args.side;d=args.free_rail_margin
        assert 0<=2*d<n
        rows=build(n)
        for i in range(d,n-d):
            for j in range(d,n-d):
                x=bits[n*i+j];f.append([x if rows[i][j]=='#' else -x])
    f.to_file(args.out);print('physical CNF',f.nv,len(f.clauses),flush=True)
