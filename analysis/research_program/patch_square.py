"""Forest-pattern local polytope on 3x3 patches of an unrestricted square."""
from collections import Counter,defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib,json
from .square_current import load,axis,DIR,lpterms
import subprocess

P=tuple(product(range(3),repeat=2))
EDGES=[(i,3*(r+a)+c+b) for i,(r,c) in enumerate(P) for a,b in DIR[:2] if r+a<3 and c+b<3]


def forest(m):
    parent=list(range(9))
    def root(i):
        while i!=parent[i]:i=parent[i]
        return i
    for i,j in EDGES:
        if (m>>i|m>>j)&1:
            a,b=root(i),root(j)
            if a==b:return False
            parent[a]=b
    return True


MASKS=tuple(m for m in range(512) if forest(m))
def local(m,i):
    r,c=P[i]
    return (m>>i&1,)+tuple((m>>(3*(r+a)+c+b))&1 for a,b in DIR if 0<=r+a<3 and 0<=c+b<3)


def patch_probs(data,r,c,n):
    ds=[]
    for i,(a,b) in enumerate(P):
        ds.append(Counter())
        dirs=[k for k,(dr,dc) in enumerate(DIR) if 0<=a+dr<3 and 0<=b+dc<3]
        for f,es,o,v in data[axis(r+a,n),axis(c+b,n)]:
            key=(f,)+tuple(es[k][1 if k<2 else 0] for k in dirs)
            ds[i][key]+=v
    return ds


def support_test():
    data=load();bad=[];allbad=[]
    n=14
    for r,c in product(range(n-2),repeat=2):
        ds=patch_probs(data,r,c,n)
        compatible=[m for m in MASKS if all(ds[i][local(m,i)] for i in range(9))]
        for i in range(9):
            for s,w in ds[i].items():
                if any(local(m,i)==s for m in compatible):continue
                # A legal completion with event (i,s) must hit at least one
                # forbidden local event. Minimize the covering set by deletion.
                pool=[m for m in MASKS if local(m,i)==s]
                ban={(j,local(m,j)) for m in pool for j in range(9) if not ds[j][local(m,j)]}
                for event in sorted(ban):
                    if all(any((j,local(m,j)) in ban-{event} for j in range(9)) for m in pool):ban.remove(event)
                assert all(any((j,local(m,j)) in ban for j in range(9)) for m in pool)
                bad.append((len(ban),r,c,i,s,sorted(ban),w));allbad.append((r,c))
    print("forest masks",len(MASKS),"nonextending patches via support",len(set(allbad)))
    if bad:print("shortest support cover",min(bad))
    # A 111 rail on the right edge leaves at most one selected site in
    # the entire remaining (left) column. This is exactly the cover used below.
    idx=(1,1,0,1);pool=[m for m in MASKS if local(m,5)==idx]
    ban=[(1,(0,1,0,1)),(3,(0,0,0,0)),(4,(0,1,0,1,0)),(7,(0,1,1,0))]
    assert pool==[292,293,300,356]
    assert all(sum(local(m,i)==z for i,z in ban)==1 for m in pool)
    ds=patch_probs(data,2,2,17)
    print("3x3 rail event:",ds[5][idx],"cover sum",sum(ds[i][s] for i,s in ban),
          "exact legal completions",pool)
    return bad


def trans(i,j,n,s):
    if s&4:j=n-1-j
    for _ in range(s&3):i,j=j,n-1-i
    return i,j


def transformed(m,s):
    return sum(1<<(3*u+v) for i,(r,c) in enumerate(P) if m>>i&1 for u,v in [trans(r,c,3,s)])


SYM={m:[transformed(m,s) for s in range(8)] for m in MASKS}
def relaxation(n,depth=None,patch=True,cut=False,pooled=None,period=1,tags=None,strip_cut=False,diagonal=None,rooted=False,group_override=None,accept=None,rays=None):
    # Average over the square symmetries. Corners are equiprobable roots
    # in the orientation: each must be a sink with probability >=1/4.
    def ax(i,size):
        if depth is None:return i
        d=depth if size==n else depth-1
        assert size>=2*d+period
        return i if i<d else 2*d+period-size+i if i>=size-d else d+(i-d)%period
    names={};rows={}
    group=(0,7) if rooted else tuple(range(8))
    if group_override is not None:group=group_override
    maskgroup=tuple(range(8)) if rooted=='shared' else group
    def var(key):return names.setdefault(key,"x"+str(len(names)))
    def add(coeff,rhs=0,op='=',tag=None):
        coeff={x:v for x,v in coeff.items() if v}
        if not coeff:assert rhs==0;return
        first=min(coeff)
        sign=-1 if coeff[first]<0 and op=='=' else 1
        if sign==-1:coeff={x:-v for x,v in coeff.items()};rhs=-rhs
        key=tuple(sorted(coeff.items())),op,rhs
        if tags is not None and key not in rows:tags.append((sign,tag))
        rows[key]=None
    def diff(a,b):
        c=a.copy();c.subtract(b);return c
    def extra(i,j,S,fine):
        if diagonal is None:return ()
        # Distinguish the moving interfaces between the four closest
        # sides. The extra fine collar determines every coarse relation
        # touching this site (3-by-3 offsets and a size change of two).
        d=diagonal+(5 if fine else 0)
        return tuple(max(-d,min(d,z)) for z in (i-j,i+j+1-S)) + (rays(i,j,S,fine) if rays else ())
    def finepos(i,j,S):return (ax(i,S),ax(j,S))+extra(i,j,S,True)
    def orbit(i,j,S):
        return [finepos(a,b,S) for s in range(8) for a,b in [trans(i,j,S,s)]]
    if pooled is not None:
        # One unknown per SUM of local probabilities on a fine location
        # type. Pool the marginal constraints at a coarser spatial scale.
        # The fine type must determine the coarse types of all its neighbors.
        assert depth>=pooled+4 and patch and not cut
    def coarse(i,j,S):
        def a(t):return t if t<pooled else pooled+(t-pooled)%period if t<S-pooled else 2*pooled+period-S+t
        return (a(i),a(j))+extra(i,j,S,False)
    def pp_type(i,j,S):
        if strip_cut not in ('lift','lift4','pinned','r28'):return coarse(i,j,S)
        d=pooled+(2 if strip_cut=='lift4' else 1)
        def a(t):return t if t<d else d+(t-d)%period if t<S-d else 2*d+period-S+t
        return a(i),a(j)
    mult={S:Counter(finepos(i,j,S) for i,j in product(range(S),repeat=2)) for S in (n,n-2)}
    counts={};bucket=defaultdict(Counter)
    def pairrow(a,b,tag):
        if pooled is None:add(diff(a,b),tag=tag);return
        bucket[tag].update(a);bucket[tag].subtract(b)
    stars={};obj=Counter()
    for i,j in product(range(n),repeat=2):
        pos=orbit(i,j,n)
        dirs=[s for s,(u,v) in enumerate(DIR) if 0<=i+u<n and 0<=j+v<n]
        if pos[0] not in stars:
            from .square_current import states
            es=[]
            for f,sig in states(dirs):
                out=next((d for d,e in sig.items() if e[2]==(1 if d<2 else -1)),-1)
                if rooted and (i,j)==(0,0) and out!=-1:continue
                # Combine each star's port/arrow data into an ordered word.
                nb=[sig[s][1 if s<2 else 0] if s in sig else 9 for s in range(4)]
                if accept is not None and not accept(i,j,0,(f,tuple(nb),out)):continue
                def rot(s):
                    dc=[DIR.index(tuple(a-b for a,b in zip(trans(1+x,1+y,3,s),trans(1,1,3,s)))) for x,y in DIR]
                    return tuple(nb[dc.index(k)] for k in range(4)),(-1 if out==-1 else dc[out])
                x=var(('s',min((pos[s],f,*rot(s)) for s in group)))
                es.append((x,f,sig,out))
            stars[pos[0]]=es
            mass=1 if pooled is None else mult[n][pos[0]]
            for x,*_ in es:counts[x]=mass
            add(Counter(x for x,*_ in es),mass,tag=('star norm',pos[0]))
            if len(dirs)==2 and not rooted:add(Counter({x:4*v for x,v in Counter(x for x,f,s,o in es if o==-1).items()}),1,'>=',('corner',pos[0]))
        for x,f,_,_ in stars[pos[0]]:obj[x]+=f
    def star(i,j):return stars[finepos(i,j,n)]
    for i,j in product(range(n),repeat=2):
        for d,(a,b) in enumerate(DIR[:2]):
            if i+a>=n or j+b>=n:continue
            p=defaultdict(Counter);q=defaultdict(Counter)
            for x,_,s,_ in star(i,j):p[s[d]][x]+=1
            for x,_,s,_ in star(i+a,j+b):q[s[d+2]][x]+=1
            for k in p:pairrow(p[k],q[k],(('s',(i,j),(i+a,j+b),d,k) if tags is not None else None) if pooled is None else ('s',coarse(i,j,n),coarse(i+a,j+b,n),d,k))
    def projections(ds,idx):
        r,c=P[idx];pr=defaultdict(Counter)
        dirs=[s for s,(a,b) in enumerate(DIR) if 0<=r+a<3 and 0<=c+b<3]
        for x,f,sig,_ in ds:pr[(f,)+tuple(sig[s][1 if s<2 else 0] for s in dirs)][x]+=1
        return pr
    if cut or patch:
        tabs={}
        for i,j in product(range(n-2),repeat=2):
            if cut:
                a=projections(star(i+1,j+2),5)[1,1,0,1].copy()
                for q,s in [(1,(0,1,0,1)),(3,(0,0,0,0)),(4,(0,1,0,1,0)),(7,(0,1,1,0))]:
                    u,v=P[q];a.subtract(projections(star(i+u,j+v),q)[s])
                add(a,0,'<=')
            if not patch:continue
            pos=orbit(i,j,n-2)
            if pos[0] not in tabs:
                tab={m:var(('p',min((pos[g],SYM[m][g]) for g in maskgroup))) for m in MASKS
                     if accept is None or accept(i,j,1,m)}
                tabs[pos[0]]=tab
                if pooled is not None:
                    mass=mult[n-2][pos[0]]
                    for x in tab.values():counts[x]=mass
                    add(Counter(tab.values()),mass,tag=('patch norm',pos[0]))
            else:tab=tabs[pos[0]]
            for q,(u,v) in enumerate(P):
                pr=projections(star(i+u,j+v),q);other=defaultdict(Counter)
                for m,x in tab.items():other[local(m,q)][x]+=1
                for k in set(pr)|set(other):pairrow(pr[k],other[k],(('sp',(i,j),(i+u,j+v),q,k) if tags is not None else None) if pooled is None else
                    ('sp',coarse(i,j,n-2),coarse(i+u,j+v,n),q,k))
        if patch:
            for i,j in product(range(n-2),repeat=2):
                for a,b in DIR[:2]:
                    if i+a>=n-2 or j+b>=n-2:continue
                    pr=defaultdict(Counter);qr=defaultdict(Counter)
                    for di,dj,table in [(0,0,pr),(a,b,qr)]:
                        for m,x in tabs[finepos(i+di,j+dj,n-2)].items():
                            k=tuple((m>>(3*(y-di)+z-dj))&1 for y in range(a,3) for z in range(b,3))
                            table[k][x]+=1
                    for k in set(pr)|set(qr):pairrow(pr[k],qr[k],(('pp',(i,j),(i+a,j+b),a,b,k) if tags is not None else None) if pooled is None else
                        ('pp',pp_type(i,j,n-2),pp_type(i+a,j+b,n-2),a,b,k))
                    if strip_cut in ('pinned','r28') and (i,j,a,b)==(1,3,0,1):
                        k=(0,)*6
                        pairrow(pr[k],qr[k],('pinned',i,j,k))
                    if strip_cut=='r28' and (a,b)==(0,1):
                        # A singleton upper boundary pair, and two sums over
                        # strips transverse to it (transpose the vertical cuts).
                        k=(0,)*6
                        if (i,j)==(0,3):
                            pairrow(pr[k],qr[k],('r28',0))
                        if j==3 and 4<=i<n-2-4 and (i-4)%3 in (0,1):
                            pairrow(pr[k],qr[k],('r28',1+(i-4)%3))
    if strip_cut:
        assert pooled is not None
        def columns(m):
            return tuple(sum((m>>(3*r+c)&1)<<r for r in range(3)) for c in range(3))
        masks={columns(m):m for m in MASKS}
        for i,j in product(range(n-2),range(n-3)):
            left=tabs[ax(i,n-2),ax(j,n-2)]
            right=tabs[ax(i,n-2),ax(j+1,n-2)]
            for u,v in ((1,4),(4,1)):
                tag=('strip',coarse(i,j,n-2),coarse(i,j+1,n-2),u,v)
                c=bucket[tag]
                c[left[masks[5,u,v]]]+=1
                c[right[masks[u,v,5]]]+=1
                for w,m in masks.items():
                    if w[1:]==(u,v):c[left[m]]-=1
    if pooled is not None:
        for tag,c in bucket.items():
            assert all(w%counts[x]==0 for x,w in c.items())
            add({x:w//counts[x] for x,w in c.items()},0,'<=' if tag[0]=='strip' else '=',tag=tag)
        assert all(w%counts[x]==0 for x,w in obj.items())
        obj=Counter({x:w//counts[x] for x,w in obj.items()})
    return names,rows,obj


def verify_upper(rows,obj,ys):
    residual=Counter(obj);base=Q(0)
    for i,(c,o,v) in enumerate(rows):
        y=ys.get(i,Q(0))
        if o=='>=':y=min(0,y)
        if o=='<=':y=max(0,y)
        base+=y*v
        for x,w in c:residual[x]-=w*y
    err=sum(max(z,0) for z in residual.values())
    return base+err,err


def signature(rows,obj):
    return hashlib.sha256(repr((list(rows),sorted(obj.items()))).encode()).hexdigest()


def replay_upper(n=17):
    p=Path(__file__).with_name(f'patch_square_{n}_dual.json')
    d=json.loads(p.read_text());_,rows,obj=relaxation(n)
    assert signature(rows,obj)==d['model']
    upper,err=verify_upper(rows,obj,{i:Q(y) for i,y in d['multipliers']})
    limit={6:17,9:35,17:111,23:197,26:249,28:290,29:307,31:352,32:371,34:421,35:441,37:495,38:516,40:575,41:598,43:662,46:754,49:852}[n]
    assert upper<limit
    print("solver-free unrestricted",n,"square upper",upper,"<",limit,"residual allowance",err)


def replay_primal_34():
    names,rows,obj=relaxation(34)
    y={x:Q(q) for x,q in json.loads(Path(__file__).with_name('patch_square_34_primal.json').read_text()).items()}
    assert y.keys()<=set(names.values()) and min(y.values())>=0
    for row,op,b in rows:
        z=sum(w*y.get(x,0) for x,w in row)
        assert {'=':z==b,'<=':z<=b,'>=':z>=b}[op]
    score=sum(w*y.get(x,0) for x,w in obj.items())
    assert score>420
    print('verified fractional score',score,'> 420; unpooled constraints',len(rows))


def opt(n,depth=None,patch=True,cut=False,dual=False,shadow=False,raw=False,save=False):
    names,rows,obj=relaxation(n,depth,patch,cut)
    text="max: "+lpterms(obj)+";\n"+"".join(f"r{i}: "+lpterms(dict(c))+f" {o} {v};\n" for i,(c,o,v) in enumerate(rows))
    print("LP",n,depth,patch,cut,len(names),len(rows),flush=True)
    if dual:
        tr=defaultdict(Counter);rhs={};free=[]
        for i,(c,o,v) in enumerate(rows):
            y=f'x{i}';sign=-1 if o=='>=' else 1
            if o=='=':free.append(y)
            rhs[y]=sign*v
            for x,w in c:tr[x][y]=w*sign
        text="min: "+lpterms(rhs)+";\n"+"".join(lpterms(cs)+f" >= {obj[x]};\n" for x,cs in tr.items())+"free "+",".join(free)+";\n"
    p=subprocess.run(['lp_solve',*([] if raw else ['-presolve']),*(['-S4'] if shadow else [])],input=text,text=True,capture_output=True,check=True)
    vals={x:Q(y) for s in p.stdout.splitlines() if len(s.split())==2
          for x,y in [s.split()] if x.startswith('x') and x[1:].isdigit()}
    print("solver",p.stdout.splitlines()[:3],flush=True)
    if shadow:
        lines=p.stdout.split('Dual values with from - till limits:')[-1].splitlines()
        ys={int(a[1:]):Q(b) for s in lines if len(s.split())==4 for a,b,_,_ in [s.split()]
            if a.startswith('r') and a[1:].isdigit()}
        upper,err=verify_upper(rows,obj,ys)
        print("shadow dual rows",len(ys),"upper",upper,"roundoff allowance",err,flush=True)
        if save:
            limit={6:17,9:35,17:111}[n]
            assert depth is None and patch and not cut and upper<limit
            rounded={i:y.limit_denominator(252) for i,y in ys.items()}
            if verify_upper(rows,obj,rounded)[0]<limit:ys=rounded
            path=Path(__file__).with_name(f'patch_square_{n}_dual.json')
            path.write_text(json.dumps(dict(model=signature(rows,obj),multipliers=[
                [i,str(y)] for i,y in sorted(ys.items()) if y]),separators=(',',':'))+'\n')
            replay_upper(n)
            return
    if dual:
        unrestricted=set(free)
        vals={x:(q if x in unrestricted else max(0,q)) for x,q in vals.items()}
        # Bound dual residual via the normalization of each variable.
        # Every x is an actual (possibly symmetrized) event probability <=1.
        err=sum(max(Q(0),obj[x]-sum(w*vals[y] for y,w in cs.items())) for x,cs in tr.items())
        ub=sum(w*vals[y] for y,w in rhs.items())+err
        print('rational upper',ub,'roundoff allowance',err,flush=True)
        return ub
    # Recover the exact values on the positive support using the active
    # equalities. lp_solve's text output rounds to only six digits.
    support={x for x,v in vals.items() if v>Q(1,100000000)}
    pivots={}
    for c,o,b in rows:
        if o!='=' and abs(sum(w*vals[x] for x,w in c)-b)>Q(1,10000):continue
        row={x:Q(w) for x,w in c if x in support};v=Q(b)
        while row:
            x=min(row,key=lambda s:int(s[1:]));k=row[x]
            if x not in pivots:
                del row[x];pivots[x]=({y:a/k for y,a in row.items()},v/k);break
            pc,pb=pivots[x];v-=k*pb;del row[x]
            for y,w in pc.items():
                row[y]=row.get(y,0)-w*k
                if not row[y]:del row[y]
    vals={x:(v if x in support else Q(0)) for x,v in vals.items()}
    for x in sorted(pivots,key=lambda s:-int(s[1:])):
        pc,pb=pivots[x];vals[x]=pb-sum(w*vals[y] for y,w in pc.items())
    assert min(vals.values())>=0
    for c,o,v in rows:
        z=sum(k*vals[x] for x,k in c)
        assert (z==v if o=='=' else z<=v if o=='<=' else z>=v),(c,o,v,z)
    f=sum(v*vals[x] for x,v in obj.items())
    print('verified primal',f,flush=True)
    return names,rows,obj,vals


if __name__=="__main__":
    import sys
    if len(sys.argv)==1:support_test()
    elif sys.argv[1]=='--primal34':replay_primal_34()
    elif sys.argv[1]=='--replay':replay_upper(int(sys.argv[2]) if len(sys.argv)>2 else 17)
    else:opt(int(sys.argv[1]),None if sys.argv[2]=='all' else int(sys.argv[2]),sys.argv[3]=='patch',sys.argv[3]=='cut','--dual' in sys.argv,'--shadow' in sys.argv,'--raw' in sys.argv,'--save' in sys.argv)
