"""All-height prefix strips with two disjoint sets of wired end contacts."""
from collections import Counter,defaultdict
from .side28_score import solve
import sys

def flow(w,depth):
    assert w>=5
    l=(w-3)//2;core=7<<l;center=2<<l;allbits=(1<<w)-1
    rails=sum(1<<x for x in range(w) if (x-l-1)%3==0)
    ini=(-1,0,(0,)*(w+1),0);states=[ini];ids={ini:0};arcs=[]
    for u,(old,pend,p,flag) in enumerate(states):
        first=old<0;a=rails if first else old
        avail=rails if first else allbits&~(old<<1|old>>1);v=avail
        while True:
            q=[*p,*range(w+1,2*w+1)]
            def rt(i):
                while q[i]!=i:i=q[i]
                return i
            def join(i,j):
                i,j=rt(i),rt(j);q[i]=j;return i!=j
            for i in range(w):
                j=w+1+i
                if ((a|v)>>i)&1 and not join(i+1,j):break
                if i and (v>>(i-1))&3 and not join(j-1,j):break
            else:
                rids=[rt(0),*[rt(w+1+i) for i in range(w)]]
                pp=tuple(rids.index(z) for z in rids)
                fresh=core&v&~a
                starts=0 if first else (fresh&~(v<<1)).bit_count()+(fresh&~(v>>1)).bit_count()
                iso=(pend&~v).bit_count()
                # flag 0 before first empty, 1 on first empty, 2 thereafter.
                mask=(v&core)>>l;nextflag=(int(mask==0) if flag==0 else 2)
                joins=int(mask==5)+int(mask==7 and flag==1)
                t=v,core&~(v|v<<1|v>>1|a),pp,nextflag
                z=ids.setdefault(t,len(ids))
                if z==len(states):states.append(t)
                arcs.append((u,z,a,v,starts,iso,joins,mask.bit_count()-1))
            if not v:break
            v=(v-1)&avail
    names={'gain':'g'};A=[];rhs=[];balance=defaultdict(Counter);over=defaultdict(Counter)
    ledger=Counter(g=6);run=Counter(g=2);joins=Counter();marks=Counter(g=1)
    overlap=(1<<(w-3))-1
    def arc(a,b,stage,old,v):
        x='x'+str(len(names));names[x]=x
        if a is not None:balance[a][x]+=1
        if b is not None:balance[b][x]-=1
        L=stage,old&overlap,v&overlap;R=stage,old>>3,v>>3
        over[L][x]+=1;over[R][x]-=1
        return x
    for u,z,a,v,S,I,J,m in arcs:
        layers=[(0,0,-1)] if u==0 else [(0,0,0),*((j,j+1,j+1) for j in range(depth))]
        for j,k,stage in layers:
            x=arc((j,u),(k,z),stage,a,v)
            ledger[x]+=S+2*I;run[x]-=S;joins[x]+=2*J-S;marks[x]-=m
    for u,(v,pend,p,flag) in enumerate(states[1:],1):
        # Simultaneously attach every bottom tooth, not just its count.
        roots=[p[i+1] for i in range(w) if v>>i&1]
        if 0 in roots or len(set(roots))!=len(roots) or not flag:continue
        x=arc((depth,u),None,depth+1,v,0)
        ledger[x]+=2*pend.bit_count()
        run[x]+=2*(v&core).bit_count();joins[x]+=2*(v&core).bit_count()
    for k,cs in balance.items():A.append((list(cs.items()),'='));rhs.append(int(k==(0,0)))
    for cs in over.values():A.append((list(cs.items()),'='));rhs.append(0)
    for cs,op,b in ((ledger,'<=',4),(run,'<=',0),(joins,'<=',0),(marks,'=',1)):
        A.append((list(cs.items()),op));rhs.append(b)
    print('two-end width',w,'tail',depth,'states',len(states),'columns',len(names),flush=True)
    g,_,p=solve(A,rhs,{'g':1},names,interior=True)
    print('gain per pitch group',g,'ledger/run/join residuals',
          *(round(sum(v*p[x] for x,v in cs.items()),6) for cs in (ledger,run,joins)),flush=True)
if __name__=='__main__':flow(*map(int,sys.argv[1:]))
