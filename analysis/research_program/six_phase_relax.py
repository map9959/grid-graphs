"""Price six-row paths using a phase-pooled transfer dual, then check its exact physical face."""
from .six_joint_lp import *


def build():
    ns,A,rhs,obj,labels=core()
    keys=list(labels)
    start=(0,0,tuple(range(6)));states=(start,);links=defaultdict(list);bal=defaultdict(list)
    seen=set()
    def ft(j):return j if j<10 else 13+j-109+8 if j>=101 else 10+(j-10)%3
    for j in range(109):
        arcs,states=layer(states)
        for s,c,d,ms in arcs:
            src=ft(j),s;dst=(ft(j+1),d) if j<108 else None
            evtype=axis(j-2,107) if j>=2 else -1
            ck=(src,c,dst,evtype)
            if ck in seen:continue
            seen.add(ck);x=f'z{len(seen)}';ns[ck]=x
            bal[src].append((x,1))
            if dst is not None:bal[dst].append((x,-1))
            if j>=2:
                for r,m in enumerate(ms):links[evtype,r,m].append((x,1))
    base=len(A)
    for k in keys:A.append((tuple(links[k]+[(labels[k],-1)]),'='));rhs.append(0)
    for k,cs in sorted(bal.items()):A.append((tuple(cs),'='));rhs.append(int(k==(0,start)))
    return ns,A,rhs,obj,base,keys


if __name__=='__main__':
    from .side28_score import solve
    ns,A,b,obj,base,keys=build();print('pooled arcs',len(ns)-7317,flush=True)
    opt,y,v=solve(A,b,obj,ns);print('phase-relaxed upper candidate',opt,flush=True)
    Path('target/six_phase_candidate.json').write_text(json.dumps([y,{x:q for x,q in v.items() if q>1e-8}],separators=(',',':')))
