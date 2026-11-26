"""Check ordered three-port gluing against graph traversal, without contraction."""
from itertools import product
from .ordered_ports import partitions,glue

def reference(prev,groups,teeth):
    # Give each already rooted incoming hop its own tree and tooth. Joining
    # two such trees is forbidden whether or not they share a perimeter.
    # Unrooted incoming ends with the same name share one prefix tree.
    old=[('u',x) if x else ('t',i) for i,x in enumerate(prev)]
    n=len(teeth)
    adj={v:[] for v in [*range(n),*old]}
    exits=groups[len(prev):]
    for u,v in zip(old,groups[:len(prev)]):
        adj[u].append(v);adj[v].append(u)
    todo=set(adj);names={}
    while todo:
        start=todo.pop();comp=[start]
        for u in comp:
            for v in adj[u]:
                if v in todo:comp.append(v);todo.remove(v)
        tooth=sum((u[0]=='t' if isinstance(u,tuple) else teeth[u]) for u in comp)
        outgoing=[i for i,v in enumerate(exits) if v in comp]
        if (sum(len(adj[u]) for u in comp)!=2*(len(comp)-1)
            or tooth>1 or not (tooth or outgoing)):return
        for v in comp:names[v]=None if tooth else min(outgoing)
    ids={None:0}
    result=tuple(ids.setdefault(names[v],len(ids)) for v in exits)
    return result,tuple(ids[names['u',i]] for i in range(1,max(prev,default=0)+1))

def check():
    n=valid=0
    for g in partitions(6):
        # Enumerate ordinary partitions into local trees, with no distinguished root.
        if g[0] or set(g)!=set(range(max(g)+1)) or any(
                g.index(i)>g.index(i+1) for i in range(max(g))):continue
        for teeth in product((0,1),repeat=max(g)+1):
            trees=[1+2*t for t in teeth]
            for i,v in enumerate(g):trees[v]|=4<<i
            for p in partitions(3):
                result=reference(p,g,teeth)
                assert glue(3,3,trees,p,3,True)==result
                n+=1;valid+=result is not None
    print('3-in / 3-out graph traversal agrees on',n,'glues;',valid,'legal')
if __name__=='__main__':check()
