"""Couple the entire realized-edge subset at a junction to the actual owned slots."""
from collections import Counter,defaultdict
from itertools import product
from .patch_square import trans
from .skeleton_exit_chart import DIR


def lift(ns,A,b,n,d,w):
    h=d+4
    def pos(i,j,t):
        def ax(z):return z if z<t else 2*t+3+z-n if z>=n-t else t+(z-t)%3
        W=w+(5 if t==h else 0);cl=lambda u:max(-W,min(W,u))
        return ax(i),ax(j),cl(i-j),cl(i+j+1-n)
    reps={pos(i,j,h):(i,j) for i,j in product(range(n),repeat=2)}
    def images(i,j,nb,o,mask):
        ans=set()
        for g in range(8):
            rot=lambda t:((2-t if g&4 else t)+g)%4
            v=[9]*4;bits=0
            for t,z in enumerate(nb):
                v[rot(t)]=z
                if mask>>t&1:bits|=1<<rot(t)
            ans.add((pos(*trans(i,j,n,g),h),tuple(v),rot(o) if o>=0 else -1,bits))
        return ans
    def eq(c):A.append(([(x,v) for x,v in c.items() if v],'='));b.append(0)
    ends=defaultdict(lambda:[defaultdict(Counter),defaultdict(Counter)])
    mids=defaultdict(Counter);obj=Counter()
    for name,x in list(ns.items()):
        if name[0]!='s':continue
        atom=name[1]
        p,f,nb,out=atom;i,j=reps[p]
        if i%3==0 and j%3==0:
            axis=[s%2 for s in range(4) if nb[s]==1]
            if not axis:continue  # forced to zero in model()
            axis=axis[0];row=Counter({x:-1})
            for mask in range(1,16):
                if out>=0 and not(mask>>out&1):continue
                if any(mask>>t&1 and (nb[t]==9 or nb[t]==0 and (not f or t%2==axis)) for t in range(4)):continue
                imgs=images(i,j,nb,out,mask);key=('incident',f,min(imgs))
                new=key not in ns;y=ns.setdefault(key,'g'+str(len(ns)));row[y]+=1
                if not new:continue
                obj[y]=len(imgs)*min((mask&5).bit_count(),(mask&10).bit_count())
                for q,v,o,bits in imgs:
                    u,z=reps[q];H=int(v[0]==1 or v[2]==1)
                    for t in (0,2):
                        if v[t]==9:continue
                        q0=pos(u,z if t==0 else z-3,d)
                        direction=1 if o==t else -1 if bits>>t&1 else 0
                        ends[q0][int(t==2)][f,v[t],H,direction][y]+=1
            eq(row)
        elif bool(i%3)!=bool(j%3):
            for q,v,o,_ in images(i,j,nb,out,0):
                u,z=reps[q]
                if u%3:continue
                side=int(z%3==2);near=0 if side else 2
                mids[pos(u,z-z%3,d),side,v[near],f,v[2-near]][x]+=1
    match=defaultdict(Counter)
    for p,(L,R) in ends.items():
        for l in L:
            for r in R:
                z,a,H,o=l;Z,b2,K,O=r
                if o!=-O:continue
                real=(a or b2) and (z or a) and (Z or b2)
                if bool(o)!=bool(real):continue
                miss=(H-a)+(K-b2)
                if miss and (miss!=1 or real):continue
                y=ns['edgeCouple',p,l,r]='e'+str(len(ns))
                L[l][y]-=1;R[r][y]-=1
                match[p,0,z,a,b2][y]+=1;match[p,1,Z,b2,a][y]+=1
        for c in [*L.values(),*R.values()]:eq(c)
    for k in sorted(set(match)|set(mids)):
        c=match[k];c.subtract(mids[k]);eq(c)
    return obj


if __name__=='__main__':
    import json,sys
    from pathlib import Path
    from .skeleton_exit_chart import model
    ns,A,b,obj,bounds,_=model(103,4,4,43,edge_floor=True,lines=True,faces=True,isolate_cut=True)
    turns=lift(ns,A,b,103,4,4);A.append((list(obj.items()),'='));b.append(3647)
    upper='--upper' in sys.argv;sign=1 if upper else -1
    path=Path(__file__).with_name('coarse_incident_103_'+('upper' if upper else 'dual')+'.json')
    scale=10**11
    if '--save' in sys.argv:
        from .side28_score import solve
        val,dual,_=solve(A,b,{x:sign*v for x,v in turns.items()},ns,interior=True,bounds=bounds)
        y={i:round(t*scale) for i,t in enumerate(dual) if round(t*scale)}
        for i in list(y):
            op=A[i][1]
            if op=='<=':y[i]=max(y[i],0)
            if op=='>=':y[i]=min(y[i],0)
    else:y=dict(json.loads(path.read_text()))
    rc=Counter({x:sign*scale*v for x,v in turns.items()});ub=0
    for i,t in y.items():
        row,op=A[i];assert op=='=' or (t>=0 if op=='<=' else t<=0)
        ub+=b[i]*t
        for x,v in row:rc[x]-=v*t
    # Every actual frequency/flow in the lifted model can be chosen as
    # a count (or orbit average of counts) on one physical board.
    ub+=103**2*sum(v for x,v in rc.items() if v>0 and x not in bounds)
    assert ub < (73 if upper else -49)*scale
    if '--save' in sys.argv:path.write_text(json.dumps(sorted((i,t) for i,t in y.items() if t),separators=(',',':'))+'\n')
    print('exact coarse-turn '+('upper < 73' if upper else 'lower > 49')+' for all floor candidates;',
          len(A),'rows;',len(ns),'variables; signed upper bound',f'{ub}/{scale}')
