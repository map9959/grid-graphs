"""Local extensions of the sole 72-unit defect on the odd tight residue-two tail."""
from .square_dual_physical import inspect,DIR,SYM,MASKS,trans
from .square_current import states
from .tight_corner_sat import cover
from functools import lru_cache
from itertools import product,combinations
from collections import Counter

def table(n):
    fam=inspect(20)
    def axis(x,S,d):return x if x<d else 2*d+3+x-S if x>=S-d else d+(x-d)%3
    @lru_cache(None)
    def types(t,i,j):
        S=n-2*t
        return tuple(tuple(axis(x,S,6-t) for x in trans(i,j,S,g)) for g in range(8))
    @lru_cache(None)
    def patch(pos):
        return tuple(int(1008*fam['p',min(zip(pos,SYM[m]))]) if m in SYM else 1009 for m in range(512))
    @lru_cache(None)
    def star(pos,ds,out,root,corner):
        tab=[1009]*(1<<(1+len(ds)))
        for f,sig in states(ds):
            v=next((d for d,w in sig.items() if w[2]==(1 if d<2 else -1)),-1)
            if out!=v or (corner and not f) or (root and v>=0):continue
            nb=[sig[d][int(d<2)] if d in ds else 9 for d in range(4)]
            if not root and v==-1 and (f or 1 in nb):continue
            imgs=[]
            for g in range(8):
                dc=lambda d:((2-d if g&4 else d)+g%4)%4
                b=[9]*4
                for d in ds:b[dc(d)]=nb[d]
                imgs.append((f,tuple(b),dc(v) if v>=0 else -1))
            q=int(1008*fam['s',min(zip(pos,imgs))]);tab[f+sum(nb[d]<<(1+s) for s,d in enumerate(ds))]=q
        return tuple(tab)
    return types,patch,star

def window(n,region,R,tables,want=True,four=False,matching=False,query=None,free_defect=False,emit=None,orient=None,skeleton=0,exit_only=False,emit_graph=None,cross=0,domain=None,root_site=(0,0),defects=None,outward_completion=False,turn_domain=None,clause_sink=None):
    from pysat.formula import CNF,IDPool
    from pysat.card import CardEnc
    from pysat.solvers import Solver
    typ,patch,star=tables;B=R+7;M=n//2;assert region=='rim' or 2*(B+R+3)<n
    rim=region=='rim'
    if rim:ii=jj=ci=cj=(0,n)
    elif region=='interior':ii=(M-R,M+R+5);jj=ii;ci=(M,M+3);cj=ci
    elif region=='edge':ii=(0,B+R+3);jj=(M-R,M+R+5);ci=(0,B);cj=(M,M+3)
    else:ii=jj=(0,B+R+3);ci=cj=(0,B)
    # Model NW geometry for either corner; the unique chosen sink is in
    # this window only for region='root'. For region='other' root a
    # different physical corner; the stencil is D4 invariant.
    inb=lambda i,j:ii[0]<=i<ii[1] and jj[0]<=j<jj[1] and (not rim or min(i,j,n-1-i,n-1-j)<R or
                    (skeleton and min(abs(i-j),abs(i+j+1-n),abs(2*i+1-n),abs(2*j+1-n))<skeleton)
                    or (cross and min(abs(2*i+1-n),abs(2*j+1-n))<cross))
    candidate=lambda i,j:ci[0]<=i<ci[1] and cj[0]<=j<cj[1]
    if domain is not None:inb=lambda i,j:(i,j) in domain
    f=CNF() if clause_sink is None else clause_sink;vp=IDPool();flags={}
    bit=lambda i,j:vp.id(('v',i,j))
    arc=lambda i,j,d:vp.id(('a',i,j,d))
    sheet=lambda i,j:vp.id(('turn',i,j))
    def pattern(vs,values,guard,flag):
        def forbid(which,g):
            for mask,v in cover(which):f.append(g+[(-z if v>>j&1 else z) for j,z in enumerate(vs) if mask>>j&1])
        if flag:
            forbid(tuple(q!=0 and q!=72 for q in values),guard)
            forbid(tuple(q==72 for q in values),guard+[flag]);forbid(tuple(q==0 for q in values),guard+[-flag])
        else:forbid(tuple(q!=0 for q in values),guard)
    for i,j in product(range(*ii),range(*jj)):
        if not inb(i,j):continue
        if i+2<ii[1] and j+2<jj[1] and all(inb(i+a,j+b) for a,b in product(range(3),repeat=2)):
            q=patch(typ(1,i,j));k='p',i,j;z=0
            if want and not exit_only and (candidate(i,j) or free_defect) and (defects is None or k in defects) and 72 in q:z=flags[k]=vp.id(k)
            pattern([bit(i+a,j+b) for a,b in product(range(3),repeat=2)],q,[],z)
        ds=tuple(d for d,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n)
        if not all(inb(i+DIR[d][0],j+DIR[d][1]) for d in ds):continue
        ids=[arc(i,j,d) for d in ds];root=(region=='root' or rim) and (i,j)==root_site
        if orient and (i,j) in orient:
            chosen=orient[i,j]
            for d,v in zip(ds,ids):f.append([v if chosen==d else -v])
        tt=[star(typ(0,i,j),ds,out,root,len(ds)==2) for out in (-1,*ds)]
        k='s',i,j;z=0
        if want and (not exit_only or len(ds)==3) and (candidate(i,j) or free_defect) and (defects is None or k in defects) and any(72 in q for q in tt):z=flags[k]=vp.id(k)
        vs=[bit(i,j)]+[bit(i+DIR[d][0],j+DIR[d][1]) for d in ds]
        for x,y in combinations(ids,2):f.append([-x,-y])
        for g,q in zip([ids]+[[-a] for a in ids],tt):pattern(vs,q,g,z)
        for d in ds:
            a,b=DIR[d];x,y=i+a,j+b;v=arc(i,j,d);w=arc(x,y,(d+2)%4)
            for lit in (bit(i,j),bit(x,y)):f.append([-lit,v,w])
            f.extend([[-v,-w],[-v,bit(i,j),bit(x,y)],[-w,bit(i,j),bit(x,y)]])
            # A restriction of a directed tree admits a lift of compass
            # turns to two sheets along every path.
            for e,(a,b) in enumerate(DIR):
                if e==(d+2)%4 or not inb(x+a,y+b):continue
                g=[-v,-arc(x,y,e)];z1=sheet(i,j);z2=sheet(x,y)*(-1 if abs(d-e)==3 else 1)
                if turn_domain is not None and not all(u in turn_domain for u in ((i,j),(x,y),(x+a,y+b))):continue
                f.extend([g+[-z1,z2],g+[z1,-z2]])
    if matching:
        # Primal owner of a free edge (an isolated site extending its
        # component), or a face owner from the complementary dual tree.
        for i,j in product(range(*ii),range(*jj)):
            if not inb(i,j):continue
            ds=[d for d,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n]
            ex=[vp.id(('ext',i,j,d)) for d in ds];allv=[bit(i,j)]+[bit(i+DIR[d][0],j+DIR[d][1]) for d in ds]
            for x in ex:
                for v in allv:f.append([-x,-v])
            for x,y in combinations(ex,2):f.append([-x,-y])
            f.append(allv+ex)
            if outward_completion and ('s',i,j) in flags:
                assert i==2 or j==2
                f.append([-flags['s',i,j],ex[ds.index(3 if i==2 else 2)]])
            if i<n-1 and j<n-1 and all(inb(i+a,j+b) for a,b in product(range(2),repeat=2)):
                fs=[vp.id(('face',i,j,d)) for d in range(4)];f.append(fs)
                for x,y in combinations(fs,2):f.append([-x,-y])
            for d,(a,b) in enumerate(DIR[:2]):
                x,y=i+a,j+b
                if not inb(x,y):continue
                fs=[(i,j,3),(i-1,j,1)] if d==0 else [(i,j,2),(i,j-1,0)]
                owners=[ex[ds.index(d)],vp.id(('ext',x,y,(d+2)%4))]
                for I,J,e in fs:
                    if 0<=I<n-1 and 0<=J<n-1:owners.append(vp.id(('face',I,J,e)))
                for z in owners:
                    f.append([-z,-bit(i,j)]);f.append([-z,-bit(x,y)])
                for a1,b1 in combinations(owners,2):f.append([-a1,-b1])
                f.append([bit(i,j),bit(x,y)]+owners)
    if want:f.extend((CardEnc.atmost if free_defect else CardEnc.equals)(list(flags.values()),1,vpool=vp,encoding=1).clauses)
    if four:
        assert rim
        old=f.clauses[:];top=vp.top;maps=[list(range(top+1))]
        for rot in (1,2,3):
            ids=[0]
            for i in range(1,top+1):
                k=vp.obj(i)
                if k is not None and k[0]=='v':
                    I,J=trans(k[1],k[2],n,rot);z=bit(I,J)
                else:z=vp.id(('copy',rot,i))
                ids.append(z)
            f.extend([[ids[z] if z>0 else -ids[-z] for z in cs] for cs in old])
            maps.append(ids)
        corners=[trans(0,0,n,g) for g in range(4)]
        for i,j in product(range(*ii),range(*jj)):
            if not inb(i,j):continue
            ds=[d for d,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n]
            if not all(inb(i+DIR[d][0],j+DIR[d][1]) for d in ds):continue
            order=[g for g in range(4) if (i,j)!=corners[g]]
            start=next((d for d,ok in enumerate((i==0 and j<n-1,j==n-1 and i<n-1,i==n-1 and j>0,j==0 and i>0)) if ok),None)
            if start is not None:order.sort(key=lambda g:(g-1-start)%4)
            variables={}
            for g in order:
                x,y=trans(i,j,n,(-g)%4)
                for d in ds:variables[g,d]=maps[g][arc(x,y,(d-g)%4)]
            for word in product(ds,repeat=len(order)):
                if start is not None:
                    seq=[(d-start)%4 for d in word];bad=seq!=sorted(seq)
                else:bad=sum(a>b for a,b in zip(word,word[1:]+word[:1]))>1
                if bad:f.append([-variables[g,d] for g,d in zip(order,word)])
    if emit_graph is not None:return emit_graph(f,bit,flags,arc,sheet)
    if emit is not None:return emit(f,bit,flags)
    with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
        if query is not None:return query(s,bit)
        poss=[]
        while s.solve():
            if not want:return True
            vals={x for x in s.get_model() if x>0};key,= [k for k,z in flags.items() if z in vals]
            if rim:return [key]
            poss.append(key);s.add_clause([-flags[key]])
        return poss if want else False
if __name__=='__main__':
    import sys
    R=int(sys.argv[1]);n=119;t=table(n)
    if '--rim' in sys.argv:
        for w in (False,True):
            print('rim width',R,'require one defect',w,'extension',window(n,'rim',R,t,w,'--four' in sys.argv,'--matching' in sys.argv),flush=True)
    else:
        for region in ('interior','edge','other','root'):
            found=window(n,region,R,t);print(region,'surviving defect sites',len(found),sorted(found),flush=True)
