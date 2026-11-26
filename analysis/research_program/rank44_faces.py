"""Price local refills with the partition induced by the skeleton classes."""
from collections import Counter,defaultdict
from functools import lru_cache
from itertools import product
from .four_square import masks4
from .patch_square import trans,SYM,MASKS
from .skeleton_cross_rank import DSU

CORN=(0,3,12,15)
INNER=sum(1<<i for i in (5,6,9,10))
PORT=[i for i in range(16) if not INNER>>i&1]
EDGES=[(i,j) for i in range(16) for j in ([i+1] if i%4<3 else [])+([i+4] if i<12 else [])]


def canon(word):
    labels={}
    return tuple(labels.setdefault(c,len(labels)) for c in word)


def colors(q):
    return q if isinstance(q,tuple) else tuple(q>>a&1 for a in range(4))


def parts(q,g):
    word=[0]*4
    for a,c in enumerate(colors(q)):
        y,x=trans(a//2,a%2,2,g);word[2*y+x]=c
    word=canon(word)
    return word if isinstance(q,tuple) else sum(c<<a for a,c in enumerate(word))


@lru_cache(None)
def table(C,j):
    if C>4 or j>3:return table(min(C,4),min(j,3))
    partitions=(sorted({canon(w) for w in product(range(C),repeat=4)}) if C>=3
                else range(0,16,2) if C==2 else (0,))
    good={};best=defaultdict(dict)
    for m in masks4():
        sk=m&~INNER
        for partition in partitions:
            col=colors(partition)
            ds=DSU(16)
            for u,v in EDGES:
                if (sk>>u|sk>>v)&1:assert ds.join(u,v)
            if any(ds.root(u)==ds.root(v) and col[a]!=col[b]
                   for a,u in enumerate(CORN) for b,v in enumerate(CORN)):continue
            for a,u in enumerate(CORN):
                for b,v in enumerate(CORN[:a]):
                    if col[a]==col[b]:ds.join(u,v)
            old=len({ds.root(u) for u in CORN})
            for u,v in EDGES:
                if (m>>u|m>>v)&1 and not (sk>>u|sk>>v)&1 and not ds.join(u,v):break
            else:
                rank=old-len({ds.root(u) for u in CORN})
                if rank>j:continue
                p=sum(1<<(a*12+b) for a,u in enumerate(PORT) for b,v in enumerate(PORT[:a]) if ds.root(u)==ds.root(v))
                size=(m&INNER).bit_count()
                good[m,partition]=(p,size,rank)
                d=best[sk,partition];d[p]=max(d.get(p,0),size)
    return {(m,q):rank for (m,q),(p,size,rank) in good.items()
            if not any(a&~p==0 and z>size for a,z in best[m&~INNER,q].items())}


def labels(i,j,n,h):
    def ax(z):return z if z<h else 2*h+3+z-n if z>=n-h else h+(z-h)%3
    return ax(i),ax(j)


def add(ns,A,b,n,C,j,depth=2):
    S=n-3
    Q={q:[parts(q,g) for g in range(8)] for q in {q for _,q in table(C,j)}}
    reps={};kids=defaultdict(dict);horizontal=defaultdict(Counter)
    for i,k in product(range(0,S,3),repeat=2):
        ps=tuple(labels(*trans(i,k,S,g),S,depth) for g in range(8))
        reps[ps[0]]=ps
        for t,(u,v) in enumerate(product(range(2),repeat=2)):
            imgs=[]
            for g in range(8):
                a,z=trans(i+u,k+v,n-2,g);cl=lambda t:max(-9,min(9,t))
                imgs.append((*labels(a,z,n-2,7),cl(a-z),cl(a+z+1-(n-2))))
            kids[ps[0],t][imgs[0]]=tuple(imgs)
    rankrow=Counter();seen=set();md=masks4();shared=defaultdict(Counter)
    # Record shared-edge words and the relative labels of their endpoints.
    for pos,ps in sorted(reps.items()):
        sub=[defaultdict(Counter) for _ in range(4)]
        for (m,q),rank in table(C,j).items():
            ss,mm=md[m];atom=('rankFace',min((p,im,Q[q][g]) for g,(p,im) in enumerate(zip(ps,mm))))
            x=ns.setdefault(atom,'rf'+str(len(ns)))
            for t,v in enumerate(ss):sub[t][v][x]+=1
            if rank:rankrow[x]+=rank
            bit=lambda a,z:m>>(4*a+z)&1
            for a in (0,3):
                word=tuple(bit(a,z) for z in range(4))
                horizontal[pos,a,word][x]+=1
                c=colors(q);cut=c[2*(a//3)]!=c[2*(a//3)+1]
                shared[a,pos,word,cut][x]+=1
        for t,gs in enumerate(sub):
            for v in MASKS:
                cs=gs[v].copy()
                for imgs in kids[pos,t].values():cs[ns['p',min(zip(imgs,SYM[v]))]]-=1
                row=tuple(sorted(cs.items()))
                if row not in seen:seen.add(row);A.append((row,'='));b.append(0)
    # Count the same internal horizontal face boundary from above and
    # below. Use a single global sum because pooled types can have
    # multiple successors. Symmetry supplies the vertical version.
    for word,cut in product(product((0,1),repeat=4),(0,1)):
        row=Counter()
        for pos in reps:
            if pos[0]!=0:row.update(shared[0,pos,word,cut])
            if pos[0]!=labels(S-1,0,S,depth)[0]:row.subtract(shared[3,pos,word,cut])
        if any(row.values()):A.append(([(x,v) for x,v in row.items() if v],'='));b.append(0)
    if rankrow:A.append((list(rankrow.items()),'<='));b.append(j)
    return horizontal


def test(save=False,replay=False,off=44,ranges=False,components=None,weighted=False,free=False,cuts=True,allow_pitch=False,signed=False,price_pure=False,n=103):
    from .skeleton_exit_chart import model
    from .skeleton_wired_faces import face_masks
    from .skeleton_floor_words import add_lines
    from .segment_face_turns import geometry
    from .side28_score import solve
    assert {m for m,q in table(1,0)}==set(face_masks())
    counts=range(1,off-41) if components is None else (components,)
    assert all(1<=c<=off-42 for c in counts)
    planes={}
    signed=signed or allow_pitch
    if n!=103:assert free and n%3==1 and not cuts
    # Free mode uses all four-corner partitions and all possible local
    # joins. Neither catalogue index is a global component/rank bound.
    pairs=[(4,3)] if free else ((c,r) for c in counts for r in range(c))
    for C,j in pairs:
        ns,A,b,obj,bo,(F,path,sink,ex)=model(n,4,4,None if free else off,cuts=cuts,isolate_cut=cuts,allow_pitch=allow_pitch or price_pure)
        f_eq=len(A)
        if not free:
            f_cap,=(i for i,(row,op) in enumerate(A) if op=='<=' and row==list(F.items()))
            for c,r in ((F,off),(sink,C-j),(ex,j)):
                A.append((list(c.items()),'='));b.append(r)
        horizontal=add(ns,A,b,n,C,j)
        rank_cap=len(A)-1 if j else None
        if C>=1:
            # X=off-42-C at the target, under every axis assignment. Choose
            # empty-stub junctions as V when reading horizontal lines.
            marg=defaultdict(Counter)
            _,pos,jj,_=geometry(n)
            for key,x in ns.items():
                if key[0]!='s':continue
                p,f,nb,o=key[1]
                # Recover a physical representative for the fine label.
                if p not in jj:continue
                i,k=jj[p];imgs=set()
                for g in range(8):
                    rot=lambda t:((2-t if g&4 else t)+g)%4
                    v=[9]*4
                    for t in range(4):v[rot(t)]=nb[t]
                    imgs.add((pos(*trans(i,k,n,g)),tuple(v),rot(o) if o>=0 else -1))
                for t,v,_ in imgs:
                    a=(int(v[2]==1),f,int(v[0]==1))
                    if signed:
                        hs=(1,1) if a[0] or a[2] else (0,0) if v[1]==1 or v[3]==1 else (0,1)
                        for H in hs:marg[t[0],t[1],(*a,H)][x]+=1
                    else:marg[t[0],t[1],a][x]+=1
            # A placeholder RHS of zero is replaced below in the free
            # model; weighted=True always emits the debit row.
            budget=0 if free else off-42-C
            add_lines(ns,A,b,marg,n,8,exceptional=budget,weighted=weighted,signed=signed,no_pure=not allow_pitch,allow_zero=price_pure)
            exception_cap=len(A)-1 if budget or weighted else None
            # A horizontal DFA transition sees the entire four-bit
            # edge. Equate its word to both adjoining physical faces.
            role={}
            for i,k in product(range(0,n,3),range(0,n-1,3)):
                y,p=labels(i,k,n,8);q=labels(i,k+3,n,8)[1]
                tags=tuple((labels(i-a,k,n-3,2),a) for a in (0,3) if 0<=i-a<n-3)
                assert role.setdefault((y,p,q),tags)==tags
            for name,x in ns.items():
                if name[0]!='floorLine':continue
                _,y,(p,q,s,u)=name
                if p is None:continue
                word=(*s[1][1:3],*u[1][:2])
                for tag,a in role[y,p,q]:horizontal[tag,a,word][x]-=1
            for row in horizontal.values():
                A.append((list(row.items()),'='));b.append(0)
        if free:
            assert weighted and b[exception_cap]==0 and b[rank_cap]==3
            row,op=A[rank_cap];assert op=='<='
            c=Counter(dict(row));c.subtract(ex);A[rank_cap]=(list(c.items()),op);b[rank_cap]=0
            row,op=A[exception_cap];assert op=='<='
            c=Counter({x:(2 if signed else 1)*v for x,v in row});c.update(obj);c.update(sink);c.update(ex);c.subtract(F)
            if price_pure:
                for key,x in ns.items():
                    if key[0]=='floorLine' and key[2][1]==labels(0,n-1,n,8)[1] and key[2][3][0]=='p0':c[x]-=2
            A[exception_cap]=(list(c.items()),'=' if signed else op);b[exception_cap]=n*((n+2)//3)
            return ns,A,b,obj,bo,F,sink,ex
        import json
        from pathlib import Path
        tag='priced' if weighted else 'dual'
        path=Path(__file__).with_name(f'rank{off}_{tag}_{C}_{j}.json');scale=10**12
        if not replay:
            z,dual,_=solve(A,b,obj,ns,interior=True,bounds=bo)
            print('C,j',C,j,'allowed local states',len(table(C,j)),
                  'join states',sum(table(C,j).values()),'fractional optimum',z,flush=True)
            y={i:round(v*scale) for i,v in enumerate(dual) if round(v*scale)}
            for i in y:
                if A[i][1]=='<=':y[i]=max(0,y[i])
                if A[i][1]=='>=':y[i]=min(0,y[i])
        else:y=dict(json.loads(path.read_text()))
        rc=Counter({x:v*scale for x,v in obj.items()});ub=0
        for i,v in y.items():
            row,op=A[i];assert op=='=' or (v>=0 if op=='<=' else v<=0)
            ub+=b[i]*v
            for x,w in row:rc[x]-=w*v
        assert not any(bo.values())
        ub+=103**2*sum(v for x,v in rc.items() if v>0 and x not in bo)
        print('C,j',C,j,'integer upper numerator',ub,'scale',scale,flush=True)
        if replay:
            print('strict exclusion:',ub<3647*scale)
            if off<=47:assert ub<3647*scale
        if ranges and exception_cap is not None:
            # With C,j fixed, any larger F changes just these three RHSs.
            assert A[exception_cap][1]=='<=' and b[exception_cap]==off-42-C
            step=sum(y.get(i,0) for i in (f_cap,f_eq,exception_cap))
            # Coefficients for independent increments of X,C,j after
            # substituting F=42+C+X and sinks=C-j.
            planes[C,j]=(ub,step,sum(y.get(i,0) for i in (f_cap,f_eq,f_eq+1)),
                         y.get(f_eq+2,0)-y.get(f_eq+1,0)+(y.get(rank_cap,0) if j else 0))
            print('fixed C,j extrapolation: numerator step',step,'through F',
                  off+(3647*scale-1-ub)//step if step>0 else 'unbounded')
        if ranges and C>=4:
            fixed_j=sum(y.get(i,0) for i in (f_cap,f_eq,f_eq+1))
            print(f'fixed X={off-42-C},j extrapolation: numerator step',fixed_j,'through F',
                  off+(3647*scale-1-ub)//fixed_j if fixed_j>0 else 'unbounded')
            if C==4 and j in (0,1):assert ub+max(0,fixed_j)*(103**2-off)<3647*scale
        if ranges and C>=4 and j>=2:
            # Along fixed X with full-component count C-j fixed, add one
            # skeleton class and one actual join with every extra F.
            assert A[rank_cap][1]=='<=' and b[rank_cap]==j
            assert table(4,2)==table(4,3)
            step=sum(y.get(i,0) for i in (f_cap,f_eq,f_eq+2,rank_cap))
            print(f'fixed X={off-42-C},A extrapolation: numerator step',step,'through F',
                  off+(3647*scale-1-ub)//step if step>0 else 'unbounded')
            # From j=2 use both step types; the larger starting j
            # cover the remaining fixed-full-component diagonals.
            worst=max(0,step,fixed_j if j==2 else 0)
            translated=ub+worst*(103**2-off)
            if C==4:assert translated<3647*scale
            print('whole translated sector upper numerator',translated)
        if save:
            path.write_text(json.dumps(sorted((i,v) for i,v in y.items() if v),separators=(',',':'))+'\n')
    return planes


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--off',choices=range(44,52),default=44,type=int)
    p.add_argument('--components',type=int)
    p.add_argument('--save',action='store_true');p.add_argument('--replay',action='store_true')
    p.add_argument('--ranges',action='store_true')
    p.add_argument('--weighted',action='store_true')
    a=p.parse_args();test(a.save,a.replay,a.off,a.ranges,a.components,a.weighted)
