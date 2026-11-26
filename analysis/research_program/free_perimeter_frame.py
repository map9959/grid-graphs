"""One-gap target with its perimeter erased: exact independent-tooth frame DP."""
from functools import lru_cache
from .perimeter_extension import layout
import sys

@lru_cache(None)
def trans(bits,P,forced,joints,keep,retain):
    ret=[];old=len(P)
    for m in (0,1):
        p=list(P)+[old];bb=bits|m<<old
        joins=[q for q in forced if m or bits>>q&1]+[q for q in joints if m and bits>>q&1]
        for q in joins:
            a,b=p[old],p[q]
            if a==b:break
            p=[b if z==a else z for z in p]
        else:
            inds=keep+(old,) if retain else keep;u=[p[i] for i in inds]
            ret.append(((sum((bb>>j&1)<<h for h,j in enumerate(inds)),tuple(u.index(z) for z in u)),m))
    return ret

def solve(n,t,a,b,gap=True,want=False):
    N=n+t;inner=n-2;T=a+1;L=b+1
    groups=layout(inner,t+2,T,L)
    # Put the thinnest arm across the wraparound seam.
    k=min(range(0,8,2),key=lambda i:len(groups[i]));groups=groups[k:]+groups[:k]
    order=sum(groups,[]);idx={u:i for i,u in enumerate(order)}
    adj={u:set() for u in order};via={u:set() for u in order}
    for i,j in order:
        for q in ((i-1,j),(i+1,j),(i,j-1),(i,j+1)):
            if q in idx:adj[i,j].add(q)
    for i,di in ((T,-1),(T+inner-1,1)):
        for j,dj in ((L,-1),(L+inner-1,1)):
            x,y=(i+di,j),(i,j+dj);via[x].add(y);via[y].add(x)
            if gap and (i,j)==(T,L):
                x,y=(i+di,j-dj),(i-di,j+dj);via[x].add(y);via[y].add(x)
    last={v:max([idx[v]]+[idx[w] for w in adj[v]|via[v]]) for v in order}
    live=[];law={(0,()):0};hist=[]
    for s,v in enumerate(order):
        aa,bb=(tuple(sorted(live.index(w) for w in near if idx[w]<s)) for near in (adj[v],via[v]))
        keep=tuple(i for i,w in enumerate(live) if last[w]>s);retain=last[v]>s
        new={};back={}
        for (bits,P),val in law.items():
            for q,inc in trans(bits,P,aa,bb,keep,retain):
                if new.get(q,-1)<val+inc:
                    new[q]=val+inc
                    if want:back[q]=((bits,P),inc)
        law=new;live=[live[i] for i in keep]+([v] if retain else [])
        if want:hist.append(back)
    score,=law.values()
    if not want:return score
    q=(0,());marks=set()
    for v,back in reversed(list(zip(order,hist))):
        q,inc=back[q]
        if inc:marks.add(v)
    assert score==len(marks);return score,marks
if __name__=='__main__':
    n,t,a,b=map(int,sys.argv[1:5]);print('frame',n,t,a,b,solve(n,t,a,b,'--no-tooth' not in sys.argv),flush=True)
