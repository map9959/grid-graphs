"""Price a rod's outgoing slot, rather than a guessed adjacent root split."""
from .crop_frame_rate import canonical
from itertools import product


def update(state,ms,free):
    old,part=state
    # Three lane vertices and a permanent common ground. If free in
    # the frame, the new rod is identified with ground before any links.
    part=part+(part[3] if free else max(part)+1,)
    for phase,m in enumerate(ms):
        par=list(range(9))
        def rt(x):
            while x!=par[x]:x=par[x]
            return x
        def link(a,b):
            a,b=rt(a),rt(b)
            if a==b:return False
            par[a]=b;return True
        for i in range(5):par[i]=part.index(part[i])
        for i in range(3):
            if (m|old)&(1<<i) and not link(i,5+i):return
            if i and m&(3<<(i-1)) and not link(4+i,5+i):return
        if (phase==1 or m&1) and not link(5,4):return
        part=canonical(rt(x) for x in (5,6,7,3,4))
        old=m
    return old,canonical(part[:4])


def check():
    states=[(0,(0,1,2,3))]
    seen=set(states);edges=[]
    for s in states:
        for word in product(range(8),repeat=3):
            for free in (0,1):
                t=update(s,word,free)
                if t is None:continue
                if t not in seen:seen.add(t);states.append(t)
                edges.append((s,t,sum(x.bit_count() for x in word)+free-4))
    h=dict.fromkeys(states,0)
    for _ in states:
        for s,t,w in edges:h[t]=max(h[t],h[s]+w)
    ok=all(h[t]>=h[s]+w for s,t,w in edges)
    print("frame N+free <= 4p:",ok,"states",len(states),"edges",len(edges))
    assert ok


def audit_witness(p):
    from collections import defaultdict,deque
    from .triple_pocket import model,run
    data,sites,debit=model(-3,5,p,8*p-1)
    res,_=run(-3,5,p,8*p-1)
    chosen=set(res['selected']);N=sum(sites[i][0]!='C' for i in chosen)
    delta=len(chosen)-N-debit
    edges=[];rods=set();adj=defaultdict(list)
    for i,(u,v,w,cs) in enumerate(data['edges']):
        if not cs:rods.add(v)
        if not cs or any(j in chosen for j in cs):
            e=len(edges);edges.append((u,v,not cs or sites[cs[0]][0]!='C'))
            adj[u].append(e);adj[v].append(e)
    # Orient pendant edges away from each removed leaf. Each remaining
    # component of the 2-core is one cycle, orient it consistently.
    deg={u:len(vs) for u,vs in adj.items()}
    q=deque(i for i in adj if deg[i]==1)
    active=set(range(len(edges)));out={}
    while q:
        i=q.popleft()
        for e in adj[i]:
            if e not in active:continue
            assert i not in out
            active.remove(e);out[i]=e
            u,v,_=edges[e];j=u+v-i;deg[j]-=1
            if deg[j]==1:q.append(j)
    while active:
        i=edges[min(active)][0]
        while i not in out:
            e=next(e for e in adj[i] if e in active)
            active.remove(e);out[i]=e
            u,v,_=edges[e];i=u+v-i
    assert len(out)==len(edges) and len(rods)==2*p
    m=sum(i in out and not edges[out[i]][2] for i in rods)
    assert N+m<=8*p and 5*(delta-m)<=-p
    print("period, frame, paid core rods, core delta, net, upper:",
          p,N,m,delta,N+delta,8*p-(p+4)//5)


if __name__=='__main__':
    check()
    import sys
    if '--witnesses' in sys.argv:
        for p in (2,3):audit_witness(p)
