"""Stationary overlap LP for arbitrary-height wired caps, no repeated mask assumption."""
from collections import defaultdict
from itertools import product
import sys

def transitions(w,phase,classes=False):
    core=7<<(1+(w-5)//2);allbits=(1<<w)-1
    rails=sum(1<<x for x in range(w) if x%3==phase)
    sink=-1;src=-2
    def step(old,pending,part,v,first):
        q=[*part,*range(w+1,2*w+1)]
        def rt(i):
            while i!=q[i]:i=q[i]
            return i
        def join(a,b):
            a,b=rt(a),rt(b);q[a]=b;return a!=b
        for i in range(w):
            if (old|v)>>i&1 and not join(i+1,w+1+i):return
            if i and v>>(i-1)&3 and not join(w+i,w+1+i):return
        rs=[rt(0),*[rt(w+1+i) for i in range(w)]]
        p=tuple(rs.index(r) for r in rs)
        fresh=v&~old&core
        bill=0 if first else (fresh&~(v<<1)).bit_count()+(fresh&~(v>>1)).bit_count()
        if not classes:
            return (v,core&~(v|v<<1|v>>1|old),p),bill+2*(pending&~v).bit_count()
        tags=[0]*(2*w+1);tags[rs[0]]=2
        for i in range(w+1):tags[rt(i)]|=(pending>>(2*i))&3
        for i,r in enumerate(rs[1:]):
            tags[r]|=2 if i<=((core&-core).bit_length()-2) or i in (0,w-1) else (core>>i)&1
        bill+=2*sum(1 for i,t in enumerate(tags) if t==1 and i not in rs)
        flags=sum((2 if tags[r]&2 else tags[r])<<(2*i) for i,r in enumerate(rs) if i==p[i])
        return (v,flags,p),bill
    ids={};todo=[];arcs=[]
    def state(t):
        if t not in ids:ids[t]=len(todo);todo.append(t)
        return ids[t]
    def add(fr,typ,old,pending,part,allowed):
        v=allowed
        while True:
            ans=step(old,pending,part,v,typ==0)
            if ans:
                t,b=ans;arcs.append((fr,state(t),typ,old,v,b))
            if not v:break
            v=(v-1)&allowed
    add(src,0,rails,0,(0,)*(w+1),rails)
    for i,(old,pending,part) in enumerate(todo):
        add(i,1,old,pending,part,allbits&~(old<<1|old>>1))
        cc=sum((pending>>(2*i))&3==1 for i in range(w+1)) if classes else pending.bit_count()
        arcs.append((i,sink,2,old,0,2*((core&~old).bit_count()+cc)))
    return len(todo),arcs

def test(w,depth=0):
    import highspy as hs
    import numpy as np
    states,arcs=transitions(w,1,'--classes' in sys.argv)
    if depth:
        # Padding wires at the top ensures at least depth+1 rows.
        # Levels 1..depth are the last depth transitions entering tiles.
        ls=[]
        for s,t,stage,a,b,bill in arcs:
            if stage==0:ls.append((s,t,0,a,b,bill))
            elif stage==2:ls.append((s+depth*states,t,depth+2,a,b,bill))
            else:
                ls.append((s,t,1,a,b,bill))
                for j in range(depth):ls.append((s+j*states,t+(j+1)*states,2+j,a,b,bill))
        arcs=ls
    print('width',w,'states',states,'arcs',len(arcs),flush=True)
    h=hs.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
    h.setOptionValue('solver','ipm');h.setOptionValue('run_crossover','off');I=hs.kHighsInf
    n=len(arcs);h.addVars(n,np.zeros(n),np.full(n,I));h.changeColsCost(n,np.arange(n),[b for *_,b in arcs])
    rows={};ii=[];jj=[];vv=[]
    def term(key,j,val):
        ii.append(rows.setdefault(key,len(rows)));jj.append(j);vv.append(val)
    mask=(1<<(w-3))-1
    for j,(s,t,stage,a,b,_) in enumerate(arcs):
        if s!=t:
            term(s,j,1)
            if t!=-1:term(t,j,-1)
        l=(stage,a&mask,b&mask);r=(stage,a>>3,b>>3)
        if l!=r:term(l,j,1);term(r,j,-1)
    order=np.argsort(ii,kind='stable')
    starts=np.append(0,np.cumsum(np.bincount(ii,minlength=len(rows))))
    rhs=np.zeros(len(rows));rhs[rows[-2]]=1
    assert h.addRows(len(rows),rhs,rhs,len(vv),starts,np.asarray(jj)[order],np.asarray(vv)[order])==hs.HighsStatus.kOk
    h.run();print('status',h.getModelStatus(),'half-unit bill per three columns',h.getObjectiveValue(),flush=True)
if __name__=='__main__':test(*[int(z) for z in sys.argv[1:] if not z.startswith('--')])
