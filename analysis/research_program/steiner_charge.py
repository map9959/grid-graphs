"""Four simultaneous corner paths: cyclic order, displacement, turn and branching."""
from .odd_charge_parity import build,possible
from .square_dual_physical import DIR,trans
from collections import Counter,defaultdict
from itertools import product,combinations
import sys

def setup(n=35):
    old,qs,_,_,labels,rd,mass=build(n)
    keep=possible(old,qs,rd,mass,labels,(72,))
    rev={r:k for k,r in rd.items()};terms=[];rhs={};maps={};names=[];charges=[]
    def row(k):return maps.setdefault(k,len(maps))
    def push(e,cs,q):
        names.append(e);terms.append(cs);charges.append(q)
    stars=defaultdict(dict);base=defaultdict(list)
    for ok,lab,q,cs in zip(keep,labels,qs,old):
        if not ok:continue
        key,e=lab
        if key[0]==0:stars[key][e]=q;base[key,e[:2]]=cs
        else:
            push(lab,[(row(rev[r if r>=0 else ~r]),1 if r>=0 else -1) for r in cs],15 if q else 0)
    depth=6;S=n
    def ax(i):return i if i<depth else 2*depth+6+i-S if i>=S-depth else depth+(i-depth)%6
    def pt(i,j):return 0,ax(i),ax(j)
    def atomrot(e,g):
        f,nb,d=e
        return f,tuple(nb[(i-g)%4] for i in range(4)),(d+g)%4 if d>=0 else -1
    corners=[trans(0,0,n,g) for g in range(4)]
    joints=defaultdict(list)
    for k,opts in stars.items():
        _,r,c=k;i,j=[next(h for h in range(n) if ax(h)==z) for z in (r,c)]
        choices=defaultdict(lambda:[[] for _ in range(4)])
        for g in range(4):
            src=pt(*trans(i,j,n,(-g)%4))
            for e,q in stars[src].items():
                f,nb,out=atomrot(e,g);choices[f,nb][g].append((out,q))
        start=next((d for d,ok in enumerate((i==0 and j<n-1,j==n-1 and i<n-1,i==n-1 and j>0,j==0 and i>0)) if ok),None)
        for (f,nb),parts in choices.items():
            for item in product(*parts):
                ds=tuple(d for d,q in item);charge=sum((q!=0)<<g for g,(d,q) in enumerate(item))
                if ds==(-1,)*4:
                    arms=0
                else:
                    arms=len(set(ds))
                    order=[g for g in range(4) if corners[g]!=(i,j)]
                    if start is not None:
                        order.sort(key=lambda g:(g-start-1)%4);seq=[(ds[g]-start)%4 for g in order]
                        if seq!=sorted(seq):continue
                    elif sum(a>b for a,b in zip(ds,ds[1:]+ds[:1]))>1:continue
                cs=[]
                for z in base[k,(f,nb)]:
                    key=rev[z if z>=0 else ~z]
                    if key[0]=='link' and key[1:3]==(0,0):continue
                    cs.append((row(key),1 if z>=0 else -1))
                if arms>2:cs.append((row(('branch',)),arms-2))
                if arms>=2:
                    for a,b in combinations(range(4),2):
                        if ds[a]==ds[b]:continue
                        angle=lambda g:2*ds[g] if ds[g]>=0 else (5+2*g)%8
                        turn=(angle(b)-angle(a))%8-4
                        assert turn!=-4
                        if turn:cs.append((row(('turn',a,b)),turn))
                        if ds[b]>=0:
                            for h,v in enumerate(DIR[ds[b]]):
                                if v:cs.append((row(('disp',a,b,h)),v))
                joints[k].append((len(terms),f,nb,ds))
                push((k,(f,nb,ds)),cs,charge)
    for d,(a,b) in enumerate(DIR[:2]):
        parent={};used=set()
        def root(k):
            while k in parent:k=parent[k]
            return k
        for i,j in product(range(n-a),range(n-b)):
            u,v=(0,pt(i,j)),(1,pt(i+a,j+b));used.update((u,v));u,v=root(u),root(v)
            if u!=v:parent[max(u,v)]=min(u,v)
        for side,k in sorted(used):
            g=root((side,k));e=d+2*side
            for t,f,nb,ds in joints[k]:
                code=sum((v==e)<<z for z,v in enumerate(ds))
                if side and (f or nb[e]):code^=15
                pair=(nb[e],f) if side else (f,nb[e])
                terms[t].append((row(('edge',d,g,pair,code)),1 if not side else -1))
    for i,q in enumerate(charges):
        for g in range(4):
            if q>>g&1:terms[i].append((row(('charge',g)),1))
    for k,i in maps.items():
        if k[0]=='norm':
            tag,r,c=k[1];h=depth-tag;s=n-2*tag
            def count(z):return ((s-2*h+5-(z-h))//6,7) if h<=z<h+6 else (1,0)
            a,u=count(r);b,v=count(c);assert a*b==mass[k[1]]
            rhs[i]=(a*b,a*v+b*u+u*v,2*u*v)
        if k[0]=='score':rhs[i]=(440,1608,1176)
        if k[0]=='branch':rhs[i]=(2,0,0)
        if k[0]=='charge':rhs[i]=(1,0,0)
        if k[0]=='turn':_,a,b=k;rhs[i]=(2*(b-a)-4,0,0)
        if k[0]=='disp':
            _,a,b,h=k;v=corners[b][h]-corners[a][h];rhs[i]=(v,42*v//(n-1),0)
    return names,terms,charges,maps,rhs

def run():
    import highspy as H
    import numpy as np
    names,cols,qs,rows,rhs=setup()
    case=sys.argv[1] if len(sys.argv)>1 else 'any'
    allowed=[i for i,(k,e) in enumerate(names) if not qs[i] or case=='any' or (k[0]==1)==(case=='patch')]
    h=H.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
    h.setOptionValue('solver','ipm');h.setOptionValue('run_crossover','off')
    b=np.array([rhs.get(i,(0,0,0)) for i in range(len(rows))]);h.addRows(len(b),b[:,0],b[:,0],0,[],[],[])
    def put(cs):
        v=Counter()
        for i,w in cs:v[i]+=w
        h.addCol(0,0,H.kHighsInf,len(v),list(v),list(v.values()))
    for i in allowed:put(cols[i])
    for j in (1,2):put([(i,-v) for i,v in enumerate(b[:,j]) if v])
    print('Steiner uniform cone',case,len(allowed),'columns',len(b),'rows',flush=True)
    h.run();print('status',h.getModelStatus(),flush=True)
    if h.getModelStatus()==H.HighsModelStatus.kOptimal:
        v=h.getSolution().col_value;print('moments',v[-2:],'heaviest defects',sorted([(round(v[j],5),names[i]) for j,i in enumerate(allowed) if qs[i] and v[j]>1e-6],reverse=True)[:8],flush=True)
if __name__=='__main__':run()
