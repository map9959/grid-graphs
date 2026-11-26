"""Diagonal-sector chart for the exceptional residue-two single-star branches."""
from collections import Counter
from functools import lru_cache
from itertools import product
from .patch_square import relaxation,DIR
from .defect_window import table
from .odd_frames import frame
from .side28_score import solve
import sys

def run(n,word,axis,w=2):
    assert n>=77 and n%42==35 and axis in (1,2)
    T,P,S=table(n);V=frame(n,tuple(map(int,word)));g=sum(c in '02' for c in word)
    assert g in (1,2)
    if g==1:
        assert word[0]=='0'
        for i,j in product((2,n-3),repeat=2):V[i,j]=int(i==j==2)
    orient={(0,0):-1};q=[(0,0)]
    for i,j in q:
        for d,(x,y) in enumerate(DIR):
            u=i+x,j+y
            if u in V and min(*u,n-1-u[0],n-1-u[1])==0 and u not in orient and (V[i,j] or V[u]):
                orient[u]=(d+2)%4;q.append(u)
    charge={}
    @lru_cache(None)
    def context(i,j,p):
        ds=tuple(d for d,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n)
        known=tuple(V.get((i+a,j+b)) for a,b in (product(range(3),repeat=2) if p else ((0,0),*DIR)))
        return T(p,i,j),ds,known
    def accept(i,j,p,event):
        pt,ds,known=context(i,j,p)
        if p:return P(pt)[event]==0 and all(z is None or event>>h&1==z for h,z in enumerate(known))
        f,nb,out=event
        if any(z is not None and z!=v for z,v in zip(known,(f,*nb))):return False
        if (i,j) in orient and orient[i,j]!=out:return False
        if min(i,j,n-1-i,n-1-j)>=14 and i%3==j%3==2 and f and any(nb[s]==1 for s in ((0,2) if axis==1 else (1,3))):return False
        v=S(pt,ds,out,(i,j)==(0,0),len(ds)==2)[f+sum(nb[s]<<(h+1) for h,s in enumerate(ds))]
        if not f and not any(z==1 for z in nb) and not(g==1 and i==2 and v==72):return False
        return v==0 or (v==72 and (i==2 and f==0 and out==-1 and not any(z==1 for z in nb) if g==1 else len(ds)==3))
    coarse=next((int(s[9:]) for s in sys.argv if s.startswith('--coarse=')),2)
    ns,rows,obj=relaxation(n,15,pooled=coarse,period=3,diagonal=w,rooted=True,group_override=(0,),accept=accept)
    A=[];b=[]
    for row,op,z in rows:A.append((row,op));b.append(z)
    h=n//3;target=3*h*h+7*h-(h-5)//7
    print('frame',word,'axis',axis,'columns',len(ns),'rows',len(A),'target',target,flush=True)
    if '--parity' in sys.argv:
        from collections import defaultdict,deque
        atoms=list(ns.values());ix={x:i for i,x in enumerate(atoms)}
        rows2=[(row,rhs) for (row,op),rhs in zip(A,b) if op=='=']
        rows2.append((list(obj.items()),target))
        # Physical atom columns, not symmetrized probabilities.
        event=Counter()
        seen=set()
        ax=lambda v:v if v<15 else 33+v-n if v>=n-15 else 15+(v-15)%3
        cl=lambda x:max(-w-5,min(w+5,x))
        inv=defaultdict(list)
        for (p,atom),x in ns.items():
            if p=='s':inv[atom[0]].append((atom[1:],x))
        for i,j in product(range(n),repeat=2):
            typ=ax(i),ax(j),cl(i-j),cl(i+j+1-n)
            if typ in seen:continue
            seen.add(typ);pt,ds,_=context(i,j,0)
            for (f,nb,out),x in inv[typ]:
                v=S(pt,ds,out,(i,j)==(0,0),len(ds)==2)[f+sum(nb[s]<<(h+1) for h,s in enumerate(ds))]
                if v==72:event[x]=1
        cols=[0]*len(atoms);rhs=0;inc=defaultdict(list);used=defaultdict(list)
        for r,(row,z) in enumerate(rows2):
            if z&1:rhs|=1<<r
            for x,a in row:
                k=ix[x]
                if a&1:cols[k]|=1<<r
                if not z and a:
                    t=r,int(a>0);inc[t].append(k);used[k].append(t)
        live={t:len(v) for t,v in inc.items()};gone=set()
        stack=deque(t for t in inc if (t[0],1-t[1]) not in inc)
        while stack:
            for k in inc[stack.pop()]:
                if k in gone:continue
                gone.add(k)
                for r,s in used[k]:
                    live[r,s]-=1
                    if not live[r,s]:stack.append((r,1-s))
        piv={}
        def insert(v):
            while v:
                j=v.bit_length()-1
                if j not in piv:piv[j]=v;return
                v^=piv[j]
        def contains(v):
            while v:
                e=piv.get(v.bit_length()-1)
                if e is None:return False
                v^=e
            return True
        for k,x in enumerate(atoms):
            if k not in gone and x not in event:insert(cols[k])
        surv=[x for x in event if ix[x] not in gone and contains(cols[ix[x]]^rhs)]
        print('arc-pruned',len(gone),'zero-charge rank',len(piv),'single charged types passing parity',len(surv),'of',len(event))
        return
    if '--deep-count' in sys.argv:
        A.append((list(obj.items()),'='));b.append(target)
        inner={}
        for (kind,atom),x in ns.items():
            if kind!='s' or not atom[1]:continue
            r,c=atom[0][:2]
            # Fine site depth 15: far-side indices start at 18 and a
            # site n-1-j has label 32-j for 0<=j<15.
            if 13<=r<=19 and 13<=c<=19:inner[x]=-1
        val,_,_=solve(A,b,inner,ns,interior=True)
        print('deep tile deficit upper',3*(h-8)**2+val,'per deep row',(3*(h-8)**2+val)/(h-8))
    else:
        score,_,_=solve(A,b,obj,ns,interior=True);print('numerical upper minus target',score-target,flush=True)
if __name__=='__main__':run(int(sys.argv[1]),sys.argv[2],int(sys.argv[3]))
