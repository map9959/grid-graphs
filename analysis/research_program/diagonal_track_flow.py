"""An oriented-location chart lifted to an actual forest along diagonal squares."""
from itertools import product
from collections import defaultdict,Counter
from .patch_square import trans,SYM,MASKS

NW=(0,1,3,4);SE=(4,5,7,8)
def word(mask,sites):return sum((mask>>j&1)<<i for i,j in enumerate(sites))
def step(m,state):
    if state and state[0]!=word(m,NW):return
    par=list(range(9))
    def root(i):
        while par[i]!=i:i=par[i]
        return i
    if state:
        for i,p in enumerate(state[1]):par[NW[i]]=NW[p]
    for i in range(9):
        for j in ([i+1] if i%3<2 else [])+([i+3] if i<6 else []):
            if state and i in NW and j in NW:continue
            if not ((m>>i|m>>j)&1):continue
            u,v=root(i),root(j)
            if u==v:return
            par[u]=v
    roots=[root(i) for i in SE]
    return word(m,SE),tuple(roots.index(r) for r in roots)

def lift(n,ns,d,w,offsets):
    S=n-2;h=d+3;lim=w+5
    def ax(i):return i if i<h else 2*h+3+i-S if i>=S-h else h+(i-h)%3
    def pt(i,j):return (ax(i),ax(j),max(-lim,min(lim,i-j)),max(-lim,min(lim,i+j+1-S)))
    states=set(step(m,None) for m in MASKS);assert None not in states
    arcs={}
    while states-set(arcs):
        s=min(states-set(arcs));arcs[s]={}
        for m in MASKS:
            v=step(m,s)
            if v is not None:arcs[s][m]=v;states.add(v)
    rows=[]
    for off in offsets:
        assert 0<=off<lim
        coords=[(i+off,i) for i in range(S-off)]
        img={pt(i,j):tuple(pt(*trans(i,j,S,g)) for g in range(8)) for i,j in coords}
        labels=[pt(i,j) for i,j in coords];nodes=defaultdict(Counter);marg=defaultdict(Counter)
        stages=set(zip([None]+labels[:-1],labels,labels[1:]+[None]))
        for a,p,b in sorted(stages,key=repr):
            for s,transitions in ((None,{m:step(m,None) for m in MASKS}),) if a is None else sorted(arcs.items()):
                for m,u in sorted(transitions.items()):
                    x=ns.setdefault(('track',off,a,p,b,s,m),'t'+str(len(ns)))
                    if a is not None:nodes[a,p,s][x]+=1
                    if b is not None:nodes[p,b,u][x]-=1
                    marg[p,m][x]+=1
        for (p,m),cs in sorted(marg.items()):
            cs[ns['p',min(zip(img[p],SYM[m]))]]-=1
            rows.append((tuple(sorted(cs.items())),'='))
        for _,cs in sorted(nodes.items()):
            ls=tuple(sorted((x,v) for x,v in cs.items() if v))
            if ls:rows.append((ls,'='))
    return rows
