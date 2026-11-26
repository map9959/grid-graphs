"""Test exact 1/14 charge profiles on the odd residue-two progression."""
from .square_dual_physical import inspect,trans,SYM,Q
from .patch_square import relaxation,Counter
from collections import defaultdict

def profiles(W,left=72):
    if not left:yield ();return
    for j,w in enumerate(W):
        if w<=left:
            for t in profiles(W[j:],left-w):yield (w,)+t

def model():
    # A common chart for n == 5 mod 6. The coarse/fine multiplicities
    # alone change with n; the odd reflection preserves checkerboard color.
    n=23;ns,rows,obj=relaxation(n,6,pooled=2,period=6)
    sl=inspect(20);charge={};mu={};ban=set();cell={}
    def idx(i,N,d,p):return i if i<d else 2*d+p+i-N if i>=N-d else d+(i-d)%p
    for (tag,atom),x in ns.items():
        pt,*ev=atom;patch=tag=='p';N=n-2*patch;d=6-patch
        i,j=[next(t for t in range(N) if idx(t,N,d,6)==z) for z in pt]
        imgs=[];old=[]
        for g in range(8):
            rc=trans(i,j,N,g)
            pos=tuple(idx(t,N,d,6) for t in rc);co=tuple(idx(t,N,d,3) for t in rc)
            if patch:v=SYM[ev[0]][g]
            else:
                f,nb,out=ev;turn=lambda k:((2-k if g&4 else k)+g%4)%4
                word=[9]*4
                for k,s in enumerate(nb):word[turn(k)]=s
                v=f,tuple(word),turn(out) if out>=0 else -1
            imgs.append((pos,v));old.append((co,v))
        mu[x]=len(set(imgs));q=sl[tag,min(old)]*1008
        assert q.denominator==1
        charge[x]=int(q);cell[x]=(pt,d,patch)
        if not patch:
            corner=nb.count(9)==2
            if (corner and not f) or (not corner and out==-1 and (f or 1 in nb)):ban.add(x)
        if q>72:ban.add(x)
    return ns,rows,obj,cell,charge,mu,ban

def run():
    import highspy as H
    ns,rows,obj,cell,charge,mu,ban=model()
    xs=list(ns.values());ix={x:i for i,x in enumerate(xs)};W=sorted(set(q for x,q in charge.items() if x not in ban and q>0))
    todo=list(profiles(W));print('charge profiles',len(todo),W,flush=True)
    h=H.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
    h.addVars(len(xs),[0.]*len(xs),[0. if x in ban else H.kHighsInf for x in xs])
    norms=[]
    for cs,op,b in rows:
        if op=='=' and b>0:
            pt,d,p=cell[cs[0][0]];norms.append((h.getNumRow(),pt,d,p))
        h.addRow(b if op!='<=' else -H.kHighsInf,b if op!='>=' else H.kHighsInf,len(cs),[ix[x] for x,w in cs],[w for x,w in cs])
    ids={}
    for w in W:
        use=[x for x in xs if charge[x]==w and x not in ban]
        ids[w]=h.getNumRow();h.addRow(0,0,len(use),[ix[x] for x in use],[mu[x] for x in use])
    goal=h.getNumRow();h.addRow(0,0,len(obj),[ix[x] for x in obj],list(obj.values()))
    for n in (35,77,119,161,203):
        for i,pt,d,p in norms:
            S=n-2*p
            def axis(t):return t if t<d else 2*d+6+t-S if t>=S-d else d+(t-d)%6
            ct=Counter(map(axis,range(S)));z=ct[pt[0]]*ct[pt[1]];h.changeRowBounds(i,z,z)
        k=(n-2)//3;v=3*k*k+7*k-(k-5)//7;h.changeRowBounds(goal,v,v)
        valid=[]
        for pr in todo:
            cnt=Counter(pr)
            for w,i in ids.items():h.changeRowBounds(i,cnt[w],cnt[w])
            h.run();status=h.getModelStatus()
            if status==H.HighsModelStatus.kOptimal:valid.append(pr)
            else:assert status==H.HighsModelStatus.kInfeasible,status
        print('side',n,'numerically feasible charge profiles',valid,flush=True)
if __name__=='__main__':run()
