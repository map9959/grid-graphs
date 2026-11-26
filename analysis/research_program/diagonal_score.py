"""Exact physical score CNF from a sector dual: budget all local residuals."""
from .diagonal_chart import relaxation,verify,Q,Counter,Path,json,count
from .square_dual_physical import DIR,trans,SYM,MASKS
from .square_current import states
from .tight_corner_sat import cover
from itertools import combinations,product
from math import lcm
from functools import lru_cache
import sys

def require_at_least(f,pool,lits,minimum):
    """Witness a subsequence of `minimum` true literals; no upper bound."""
    assert 1<=minimum<=len(lits)
    prev=[]
    for lit in lits:
        cur=[pool.id() for _ in range(min(minimum,len(prev)+1))]
        for h,u in enumerate(cur):
            skip=prev[h:h+1]
            f.append([-u,*skip,lit])
            if h:f.append([-u,*skip,prev[h-1]])
        prev=cur
    f.append([prev[-1]])

def data(n,T):
    deep='--deep' in sys.argv
    base=(52 if n==52 else 55+(n-55)%6) if deep else 43+(n-43)%6
    d=w=4 if deep else 2
    ns,rr,obj=relaxation(base,d+4,pooled=d,period=3,diagonal=w)
    three='--three-corners' in sys.argv
    four='--four-corners' in sys.argv
    assert not (three and four)
    gaps=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--rim-gaps=')),None)
    yy=json.loads(Path(__file__).with_name(f'diagonal_d{d}_w{w}_{base}'+('_corners3' if three else '_corners4' if four else '')+(f'_rimgaps{gaps}' if gaps is not None else '')+'.json').read_text());y={int(i):Q(v) for i,v in yy.items()}
    nr=len(rr)
    if three or four:
        ss=base-2;hh=d+3
        ax=lambda u:u if u<hh else 2*hh+3+u-ss if u>=ss-hh else hh+(u-hh)%3
        cl=lambda u:max(-w-5,min(w+5,u))
        pp=[(ax(i),ax(j),cl(i-j),cl(i+j+1-ss)) for g in range(8) for i,j in [trans(0,0,ss,g)]]
        rr=list(rr)
        for z in (0,1):
            cs=Counter()
            for mask in MASKS:
                if mask&1==z and (mask>>1&1)+(mask>>3&1)==1:cs[ns['p',min(zip(pp,SYM[mask]))]]+=4
            c=3 if three else 4
            rr.append((list(cs.items()),'=',c if z else 4-c))
    if gaps is not None:
        from .sector_rim_row import row
        assert deep and not (three or four)
        rr=[*rr,(row(ns,base,d,w),'>=',2*gaps)]
    rc=Counter({x:-v for x,v in obj.items()});inv={x:k for k,x in ns.items()};ub=0;excess=0
    for i,((cs,op,b)) in enumerate(rr):
        z=y.get(i,0)
        if not z:continue
        if op=='>=':
            assert z<0
            if i<nr:assert b==1;excess-=z
        else:assert op=='='
        for x,v in cs:rc[x]+=v*z
        if b and op=='=' and i<nr:
            k,atom=inv[cs[0][0]];p=int(k=='p');b=count(n-2*p,d+4-p,w+5,atom[0])[0]
        ub+=z*b
    k=n//3;assert n%3==1 and min(rc[x] for x in ns.values())>=0
    if gaps is None:assert ub==3*k*k+Q(16*k,3)-(Q(4,3) if three else Q(7,6) if deep else 1)
    elif gaps==10:assert ub==3*k*k+Q(16*k-7,3)
    sc=8*lcm(*(z.denominator for z in y.values()));budget=int((ub-T)*sc);assert budget>=0
    def p(i,j,S,h):
        ax=lambda a:a if a<h else 2*h+3+a-S if a>=S-h else h+(a-h)%3
        clip=lambda a:max(-w-5,min(w+5,a))
        return ax(i),ax(j),clip(i-j),clip(i+j+1-S)
    def pos(i,j,tag):
        S=n-2*tag
        return tuple(p(*trans(i,j,S,g),S,d+4-tag) for g in range(8))
    @lru_cache(None)
    def patch(z):
        out=[budget+1]*512
        for m in MASKS:
            imgs=set(zip(z,SYM[m]));q=rc[ns['p',min(imgs)]]*sc/len(imgs);assert int(q)==q
            out[m]=int(q)
        return out
    @lru_cache(None)
    def star(z,dirs,extra):
        tab={o:[budget+1]*(1<<(1+len(dirs))) for o in (-1,*dirs)}
        for f,sig in states(dirs):
            out=next((s for s,v in sig.items() if v[2]==(1 if s<2 else -1)),-1)
            nb=tuple(sig[s][int(s<2)] if s in dirs else 9 for s in range(4));imgs=set()
            for g,pt in enumerate(z):
                rot=lambda x:((2-x if g&4 else x)+g)%4;ls=[9]*4
                for s in dirs:ls[rot(s)]=nb[s]
                imgs.add((pt,f,tuple(ls),rot(out) if out>=0 else -1))
            v=rc[ns['s',min(imgs)]]*sc/len(imgs)
            if extra and out==-1:v+=sc*excess
            assert int(v)==v
            tab[out][f+sum(nb[s]<<(1+j) for j,s in enumerate(dirs))]=int(v)
        return tab
    return pos,patch,star,sc,budget

def generate(n,T,domain=None,zero=False,tables=None,bill=None,variables=None):
    from pysat.formula import CNF,IDPool
    from pysat.pb import PBEnc
    pos,patch,star,sc,budget=tables or data(n,T)
    bins=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--bins=')),None)
    cap=0 if zero or not budget else bins if bins else budget
    f=CNF();pool=IDPool();X=[pool.id(('m',i)) for i in range(n*n)];weights={}
    rooted_cost='--component' in sys.argv
    if rooted_cost:assert domain is None
    wire=lambda u:pool.id(('nw-tree',u))
    def charge(tab,vs,g):
        if bins and budget and not zero:
            # A necessary relaxation: round each physical charge down,
            # preserving individual over-budget exclusions.
            tab=[cap+1 if z>budget else z*cap//budget for z in tab]
        for mask,v in cover(tuple(z>cap for z in tab)):
            f.append(g+[-x if v>>i&1 else x for i,x in enumerate(vs) if mask>>i&1])
        prev=0
        for w in sorted({z for z in tab if 0<z<=cap}):
            ind=pool.id();weights[ind]=w-prev;prev=w
            for mask,v in cover(tuple(z>=w for z in tab)):
                f.append(g+[ind]+[-x if v>>i&1 else x for i,x in enumerate(vs) if mask>>i&1])
    for i,j in product(range(n),repeat=2):
        if domain is not None and (i,j) not in domain:continue
        u=i*n+j;ds=tuple(s for s,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n)
        ids=[pool.id(('a',u,s)) for s in ds];nsites=[(i+DIR[s][0])*n+j+DIR[s][1] for s in ds]
        if u and '--local-mark-sinks' in sys.argv:
            # Root the NW component at NW and every other nontrivial
            # component at a marked vertex, in one orientation for all windows.
            for v in nsites:f.append([*ids,X[u],-X[v]])
        if u==0:
            for a in ids:f.append([-a])
        for a,b in combinations(ids,2):f.append([-a,-b])
        tab=star(pos(i,j,0),ds,len(ds)==2 and u!=0)
        if rooted_cost:
            if not u:f.append([wire(u)])
            if u:
                # Outside the NW component we may choose any marked or
                # unmarked vertex as a hypothetical sink, while retaining
                # NW as a corner sink. All charges are nonnegative.
                vs=[X[u],*[X[v] for v in nsites]]
                for mask,value in cover(tuple(q>budget for q in tab[-1])):
                    f.append([wire(u),*[-z if value>>h&1 else z for h,z in enumerate(vs) if mask>>h&1]])
                f.append([-wire(u),*ids])
                # In the actual chosen orientation root every other
                # component with edges at a marked vertex.
                for v in nsites:f.append([*ids,X[u],-X[v]])
        if domain is None or all(divmod(v,n) in domain for v in nsites):
            for s in (-1,*ds):
                charge(tab[s],[X[u]]+[X[v] for v in nsites],ids if s<0 else [-pool.id(('a',u,s))])
        for s,v,a in zip(ds,nsites,ids):
            if domain is not None and divmod(v,n) not in domain:continue
            b=pool.id(('a',v,(s+2)%4))
            if u<v:f.extend([[-a,-b],[-X[u],a,b],[-X[v],a,b],[-a,X[u],X[v]],[-b,X[u],X[v]]])
            if rooted_cost and u<v:
                for z in (X[u],X[v]):f.extend([[-z,-wire(u),wire(v)],[-z,wire(u),-wire(v)]])
            r,c=divmod(v,n)
            for e,(di,dj) in enumerate(DIR):
                if e==(s+2)%4 or not (0<=r+di<n and 0<=c+dj<n) or (domain is not None and (r+di,c+dj) not in domain):continue
                g=[-a,-pool.id(('a',v,e))];su=pool.id(('sheet',u));sv=pool.id(('sheet',v))
                if abs(e-s)==3:sv=-sv
                f.extend([g+[-su,sv],g+[su,-sv]])
        if i<n-2 and j<n-2 and (domain is None or all((i+a,j+b) in domain for a,b in product(range(3),repeat=2))):
            charge(patch(pos(i,j,1)),[X[(i+a)*n+j+b] for a,b in product(range(3),repeat=2)],[])
    if '--tooth-optimum' in sys.argv:
        # Valid for global maxima, not arbitrary forests at a lower threshold.
        from .tooth_vacancy_exchange import forbid
        forbid(f,X,n,domain)
    if '--matching' in sys.argv:
        assert domain is None
        from .sector_matching import add
        add(f,pool,X,n)
    if '--profile' in sys.argv:
        k=n//3;assert domain is None and n>=19 and T>3*k*k+5*k+(3*k-13)//10
        sides=[]
        for g in range(4):
            ls=[]
            for i in range(7):
                v=pool.id(('profile',g,i));ls.append(v);word=[]
                for j in range(n):
                    x,y=trans(i,j,n,g)
                    word.append(X[x*n+y]*(1 if j%3==0 else -1))
                f.append([v,*[-a for a in word]])
            sides.append(ls)
        for g in (0,1):
            for a in sides[g]:
                for b in sides[g+2]:f.append([-a,-b])
    if '--offrail9' in sys.argv:
        k=n//3;assert domain is None and n==3*k+1 and n>=22 and T==3*k*k+5*k+(3*k-13)//10+1
        collar=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--collar=')),None)
        minimum=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--min-collar=')),None)
        # Only normalize the sides to NW in the unanchored model.
        # With a donor, select each side independently in its physical frame.
        anchored=collar is not None or minimum is not None
        if anchored:
            from .comb_cap_transfer import construct
            from pysat.card import CardEnc
            donor=construct(n,4)
            keep=[-X[i*n+j] for i,j in product(range(n),repeat=2) if min(i,j,n-1-i,n-1-j)<=11 and donor[i][j]=='#']
            if collar is not None:f.extend(CardEnc.atmost(keep,collar,vpool=pool).clauses)
            if minimum is not None:require_at_least(f,pool,keep,minimum)
        for horizontal in (True,False):
            flag=pool.id(('offrail-side',horizontal)) if anchored else None
            for far in (range(2) if flag else (0,)):
                if '--depth10' in sys.argv:assert n==103
                for i in range(11 if '--depth10' in sys.argv else 10):
                    pts=[(n-1-r if far else r,j) for r in range(max(0,i-1),i+2) for j in range(n) if j%3]
                    f.append(([flag if far else -flag] if flag else [])+[X[r*n+j if horizontal else j*n+r] for r,j in pts])
    if '--count-marks' in sys.argv:
        assert domain is None
        from .physical_mark_count import add
        add(f,pool,X,T)
    if bill is not None:bill.update(weights)
    if weights:f.extend(PBEnc.atmost(lits=list(weights),weights=list(weights.values()),bound=cap,vpool=pool,encoding=8).clauses)
    if variables is not None:variables.update(pool.obj2id)
    print('exact charge scale',sc,'budget',budget,'CNF',f.nv,len(f.clauses),flush=True)
    return f,X
if __name__=='__main__':
    n,T=map(int,sys.argv[1:3]);f,X=generate(n,T)
    flags=[('--deep','deep'),('--three-corners','three'),('--four-corners','four'),('--matching','matching'),('--component','component'),('--profile','profile'),('--offrail9','offrail9')]
    flags.append(('--tooth-optimum','toothopt'))
    suffix=''.join('_'+z for s,z in flags if s in sys.argv)+next(('_bins'+s.split('=')[1] for s in sys.argv if s.startswith('--bins=')),'')
    suffix+=next(('_collar'+s.split('=')[1] for s in sys.argv if s.startswith('--collar=')),'')
    suffix+=next(('_mincollar'+s.split('=')[1] for s in sys.argv if s.startswith('--min-collar=')),'')
    suffix+=('_depth10' if '--depth10' in sys.argv else '')+('_count' if '--count-marks' in sys.argv else '')
    f.to_file(f'target/sector{n}_{T}{suffix}.cnf')
