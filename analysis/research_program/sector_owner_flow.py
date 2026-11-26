"""Sector-pooled allocation of edge midpoints to primal sites and bounded faces."""
from collections import Counter,defaultdict
from itertools import product
from .patch_square import DIR,trans,MASKS,SYM
from .square_current import states

def lift(ns,n,d,w):
    def tag(i,j,S,fine):
        a=d+4-int(S!=n) if fine else d
        ax=lambda x:x if x<a else 2*a+3+x-S if x>=S-a else a+(x-a)%3
        b=w+5 if fine else w
        return (ax(i),ax(j),max(-b,min(b,i-j)),max(-b,min(b,i+j+1-S)))
    def edge(u,v):
        u,v=sorted((u,v))
        return int(u[0]!=v[0]),tag(*u,n,False),tag(*v,n,False)
    demand=defaultdict(Counter);supply=defaultdict(Counter)
    root=('root',)
    for S in (n,n-2):
        seen=set()
        for i,j in product(range(S),repeat=2):
            pt=tag(i,j,S,True)
            if pt in seen:continue
            seen.add(pt)
            ps=[tag(*trans(i,j,S,g),S,True) for g in range(8)]
            if S==n:
                ds=[s for s,(u,v) in enumerate(DIR) if 0<=i+u<n and 0<=j+v<n]
                es={s:edge((i,j),(i+DIR[s][0],j+DIR[s][1])) for s in ds}
                for f,sg in states(ds):
                    nb=tuple(sg[s][int(s<2)] if s in ds else 9 for s in range(4))
                    out=next((s for s,v in sg.items() if v[2]==(1 if s<2 else -1)),-1)
                    opts=[]
                    for g,p in enumerate(ps):
                        rot=lambda s:((2-s if g&4 else s)+g)%4
                        v=[9]*4
                        for s in ds:v[rot(s)]=nb[s]
                        opts.append((p,f,tuple(v),rot(out) if out>=0 else -1))
                    x=ns['s',min(opts)]
                    free=[s for s in ds if not (f or nb[s])]
                    for s in free:
                        if s<2:supply[es[s]][x]+=1
                    if out==-1:
                        keys=[es[s] for s in free]
                        if len(ds)==2:keys.append(root)
                        demand[tuple(sorted(keys,key=str))][x]+=1
            else:
                # Charge each face to its NW-anchored patch; at the
                # southern/eastern end the last patch owns the extra face.
                for u,v in product(range(1+int(i==S-1)),range(1+int(j==S-1))):
                    uv=((u,v),(u+1,v),(u+1,v+1),(u,v+1))
                    es=[edge((i+a,j+b),(i+c,j+e)) for (a,b),(c,e) in zip(uv,uv[1:]+uv[:1])]
                    for m in MASKS:
                        bits=[m>>(3*a+b)&1 for a,b in uv]
                        keys=tuple(sorted((es[t] for t in range(4) if not(bits[t] or bits[(t+1)%4])),key=str))
                        demand[keys][ns['p',min(zip(ps,SYM[m]))]]+=1
    # Allocate each unit of demand to one of its allowed incident edge
    # buckets; no incoming/outgoing pattern is identified across copies.
    rows=[]
    for k,(keys,cs) in enumerate(demand.items()):
        for s,e in enumerate(keys):
            x=f'owner_{k}_{s}';ns['owner',(k,s)]=x
            cs[x]-=1;supply[e][x]-=1
        rows.append((list(cs.items()),'=',0))
    for e,cs in supply.items():rows.append((list(cs.items()),'=',-1 if e==root else 0))
    return rows
