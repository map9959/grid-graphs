"""Price deletion to a wired crop by thinning the teeth of each old boundary arc."""
from functools import lru_cache

@lru_cache(None)
def step(k,old,p,v):
    par=[*p,*range(k,2*k)]
    def rt(a):
        while par[a]!=a:a=par[a]
        return a
    def edge(a,b):
        a,b=rt(a),rt(b);par[a]=b;return a!=b
    for i in range(k):
        if old>=0 and (old|v)>>i&1 and not edge(i,k+i):return
        if i and v>>(i-1)&3 and not edge(k+i-1,k+i):return
    roots=tuple(rt(i) for i in range(2*k));out=roots[k:]
    return tuple(out.index(a) for a in out),roots

def graph():
    initial=(-1,(0,1,2),(0,1),0,2,2);states=[initial];ids={initial:0};arcs=[]
    for i,(old,full,p,tags,dist,greedy) in enumerate(states):
        for v in range(8):
            if old>=0 and old&(v<<1|v>>1):continue
            F=step(3,old,full,v);S=step(2,old,p,v)
            if F is None or S is None:continue
            pp,roots=S;out=roots[2:];t={roots[j] for j in range(2) if tags>>j&1}
            tooth=bool(v&4)
            if tooth:t.add(out[1])
            close=len(t-set(out));tag=sum(1<<j for j,a in enumerate(out) if pp[j]==j and a in t)
            accept=tooth and greedy==2
            bill=(v&3).bit_count()+close+int(tooth and dist==2)-int(accept)
            u=(v,F[0],pp,tag,0 if tooth else min(2,dist+1),0 if accept else min(2,greedy+1))
            j=ids.setdefault(u,len(ids))
            if j==len(states):states.append(u)
            arcs.append((i,j,bill))
    return states,arcs

def rate():
    states,arcs=graph();cost={0:0};seen={}
    for n in range(1,150):
        nxt={}
        for i,j,v in arcs:
            if i in cost:nxt[j]=max(nxt.get(j,-10000),cost[i]+v)
        mx=max(v+states[j][3].bit_count() for j,v in nxt.items());key=frozenset((j,v-mx) for j,v in nxt.items())
        if key in seen:
            k,b=seen[key];print('states',len(states),'period',n-k,'gain',mx-b,'from width',k,'price',b)
            return
        seen[key]=(n,mx);cost=nxt
    raise ValueError('no recurrence')
if __name__=='__main__':rate()
