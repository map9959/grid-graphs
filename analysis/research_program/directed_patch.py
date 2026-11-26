"""Joint 3x3 forest masks and all internal edge directions on diagonal sectors."""
from .patch_square import MASKS,SYM,DIR,trans,Counter
from itertools import product
from functools import lru_cache
from collections import defaultdict

@lru_cache(None)
def tiles():
    out=[]
    for m in MASKS:
        adj=[[] for _ in range(9)]
        for u in range(9):
            i,j=divmod(u,3)
            for d,(a,b) in enumerate(DIR[:2]):
                v=3*(i+a)+j+b
                if i+a<3 and j+b<3 and ((m>>u)|(m>>v))&1:adj[u].append((v,d));adj[v].append((u,d+2))
        parts=[];remaining=set(range(9))
        while remaining:
            u=min(remaining);comp=[u];remaining.remove(u)
            for x in comp:
                for v,_ in adj[x]:
                    if v in remaining:comp.append(v);remaining.remove(v)
            parts.append(comp)
        for roots in product(*parts):
            ds=[-1]*9;todo=list(roots);seen=set(todo)
            for u in todo:
                for v,d in adj[u]:
                    if v not in seen:seen.add(v);todo.append(v);ds[v]=(d+2)%4
            imgs=[]
            for g in range(8):
                z=0
                for u,d in enumerate(ds):
                    if d<0:continue
                    i,j=trans(*divmod(u,3),3,g);e=((2-d if g&4 else d)+g)%4
                    z+=(e+1)*5**(3*i+j)
                imgs.append((SYM[m][g],z))
            ev=[]
            for u,d in enumerate(ds):
                i,j=divmod(u,3);dirs=[s for s,(a,b) in enumerate(DIR) if 0<=i+a<3 and 0<=j+b<3]
                ev.append(((m>>u)&1,tuple((m>>(3*(i+DIR[s][0])+j+DIR[s][1]))&1 for s in dirs),d))
            overlap=[]
            for a,b in DIR[:2]:
                for side in range(2):
                    co=[(i-side*a,j-side*b) for i,j in product(range(a,3),range(b,3))]
                    overlap.append(tuple(((m>>(3*i+j))&1,ds[3*i+j] if ds[3*i+j]>=0 and (i+DIR[ds[3*i+j]][0],j+DIR[ds[3*i+j]][1]) in co else -1) for i,j in co))
            out.append((m,tuple(imgs),tuple(ev),tuple(overlap)))
    return out

def lift(n,ns,d,w):
    S=n-2
    def p(i,j,S,axd,diag):
        ax=lambda a:a if a<axd else 2*axd+3+a-S if a>=S-axd else axd+(a-axd)%3
        clip=lambda z:max(-diag,min(diag,z))
        return ax(i),ax(j),clip(i-j),clip(i+j+1-S)
    def imgs(i,j,S,axd,diag):return tuple(p(*trans(i,j,S,g),S,axd,diag) for g in range(8))
    qs={};maps=[];fines=defaultdict(dict);ss=defaultdict(dict)
    qtype=lambda i,j:p(i,j,S,d,w)
    for i,j in product(range(S),repeat=2):
        at=imgs(i,j,S,d,w);k=at[0];qs[k]=at
        pt=imgs(i,j,S,d+3,w+5);fines[k][pt[0]]=pt
        for u,(a,b) in enumerate(product(range(3),repeat=2)):
            z=imgs(i+a,j+b,n,d+4,w+5);ss[k,u][z[0]]=(i+a,j+b,z)
    uniq=set();rows=[]
    def emit(c):
        cs=tuple(sorted((x,w) for x,w in c.items() if w))
        if not cs:return
        if cs[0][1]<0:cs=tuple((x,-w) for x,w in cs)
        if cs not in uniq:uniq.add(cs);rows.append((cs,'='))
    by={}
    from .square_current import states
    @lru_cache(None)
    def stars(i,j,z):
        ds=[s for s,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n];out=[]
        for f,sig in states(ds):
            nb=tuple(sig[s][int(s<2)] if s in ds else 9 for s in range(4))
            dr=next((s for s,e in sig.items() if e[2]==(1 if s<2 else -1)),-1);images=[]
            for g in range(8):
                turn=lambda s:((2-s if g&4 else s)+g)%4;bb=[9]*4
                for s in ds:bb[turn(s)]=nb[s]
                images.append((z[g],f,tuple(bb),turn(dr) if dr>=0 else -1))
            out.append((f,nb,dr,ns['s',min(images)]))
        return out
    for k,at in sorted(qs.items()):
        law=defaultdict(Counter);starm=[defaultdict(Counter) for _ in range(9)];ov=[defaultdict(Counter) for _ in range(4)]
        for m,vv,ev,over in tiles():
            key='dir',min(zip(at,vv));x=ns.setdefault(key,'t'+str(len(ns)));law[m][x]+=1
            for u,e in enumerate(ev):starm[u][e][x]+=1
            for u,e in enumerate(over):ov[u][e][x]+=1
        by[k]=ov
        for m,c in law.items():
            for pos in fines[k].values():c[ns['p',min(zip(pos,SYM[m]))]]-=1
            emit(c)
        for u,tab in enumerate(starm):
            a,b=divmod(u,3);dirs=[s for s,(dr,dc) in enumerate(DIR) if 0<=a+dr<3 and 0<=b+dc<3]
            for i,j,z in ss[k,u].values():
                for f,nb,dr,x in stars(i,j,z):tab[f,tuple(nb[s] for s in dirs),dr if dr in dirs else -1][x]-=1
            for c in tab.values():emit(c)
    for d0,(a,b) in enumerate(DIR[:2]):
        parent={};seen=set()
        def root(u):
            while u in parent:u=parent[u]
            return u
        for i,j in product(range(S-a),range(S-b)):
            u,v=(0,qtype(i,j)),(1,qtype(i+a,j+b));seen.update((u,v));u,v=root(u),root(v)
            if u!=v:parent[max(u,v)]=min(u,v)
        groups=defaultdict(list)
        for u in seen:groups[root(u)].append(u)
        for group in groups.values():
            acc=defaultdict(Counter)
            for side,k in group:
                for e,c in by[k][2*d0+side].items():(acc[e].subtract if side else acc[e].update)(c)
            for c in acc.values():emit(c)
    return rows
