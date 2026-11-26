"""Positive full-mask control from a separately replayed physical region."""
from .absolute_port_fan import unit
from .absolute_ports import Words,column,symbols
from .joined_arm_budget import layout,row,spectrum,physical
from .component_debt import star_union

def physical_partitions(cols,start,k):
    """Independently label the suffix classes by adding actual marked sites."""
    N=3*k;par={};rooted={}
    def find(u):
        while u!=par[u]:par[u]=par[par[u]];u=par[u]
        return u
    def add(i,west):
        marks=[(3*i+b//3,3*y+b%3) for y,m in enumerate(cols[i-start])
               for b in range(9) if m>>b&1]
        for u in marks:
            x,y=u;par[u]=u;rooted[u]=x in (1,N-2) or y in (1,N-2)
        for u in marks:
            x,y=u
            for dx,dy in ((1,0),(0,1)):
                v=(x+dx,y+dy)
                if v not in par:v=(x+2*dx,y+2*dy)
                if v in par:
                    a,b=find(u),find(v)
                    assert a!=b and not(rooted[a] and rooted[b])
                    par[a]=b;rooted[b]|=rooted[a]
        names={};part=[]
        for j,m in enumerate(west):
            for h in range(3):
                code=(m>>(2*h))&3
                if code:
                    a=find((3*i+int(code==3),3*j+h))
                    part.append(0 if rooted[a] else names.setdefault(a,len(names)+1))
        return tuple(part)
    return add

def check(limit=4,t=0,axis=1):
    import sys
    sys.setrecursionlimit(5000)
    assert limit in (4,5)
    masks={m for i in range(13) for j in range(13) for w in star_union(i,j) for m in w}
    assert all(m.bit_count()<=3 for m in masks)
    k,H,_=layout(t);s=k-4*H//3
    bits,get=spectrum(7,4,axis,True,0,True,s,True)
    cap=get((bits&-bits).bit_length()-1)
    cap=cap[:s+5]+[cap[s+4]]*(14*t)+cap[s+5:]
    region=[(*a,*b) for a,b in zip(cap,zip(*(row(k,q)[1] for q in reversed(range(H)))))]
    cols=list(zip(*region));start=k-len(cols)
    assert physical(region,start,k,axis,True,require_roots=True)[1]==0
    partition=physical_partitions(cols,start,k)
    old=(0,)*k;parts={()};peak=cost=0;first=k
    for i in reversed(range(start+1,k)):
        j=i-start;rows=list(zip(cols[j-1],cols[j],cols[j+1] if i+1<k else [0]*k))
        r=38-(k-1-i) if k-1-i<7 else 7
        full=[symbols(r,w,True) for w in rows]
        west,east=zip(*full);assert old==east
        traffic=sum(bool((sym>>(2*h))&3) for sym in west for h in range(3))
        if traffic>limit:break
        first=i
        projected=tuple(symbols(r,w,b in (0,k-1))[0] for b,w in enumerate(rows))
        src,u=unit(old,parts);dst=Words();loss=sum(3-w[1].bit_count() for w in rows)
        v=column(src,u,dst,axis,r,-4,k,limit,loss,observed=projected,reverse=True,full_masks=True)
        for a in west:v=dst.nodes[v][a]
        parts={p for p,b in dst.nodes[v].items() if b>>loss&1}
        assert parts=={partition(i,west)}
        assert all(len(p)==traffic for p in parts)
        peak=max(peak,traffic)
        cost+=loss
        old=west;dst.merge.cache_clear()
    print('all',len(masks),'catalogue masks have nonnegative loss')
    if limit==5:assert peak==5
    print('axis',axis,'k',k,'physical suffix',first,'through',k-1,'at exact cost',cost,'peak',peak)
    return first,old,parts,cost

def extension(axis):
    """Free every column west of the accepted side-623 suffix, for five steps."""
    first,sym,ps,_=check(5,12,axis)
    src,u=unit(sym,ps)
    # Even relax the isolate offset at entry. This is a support test,
    # independent of the unused deficit budget of 194.
    roots=dict.fromkeys(range(-4,6),u)
    for i in range(first-1,first-6,-1):
        dst=Words();nxt={}
        for d,u in roots.items():
            v=column(src,u,dst,axis,7,d,207,5,0,False,reverse=True,full_masks=True)
            for e in ((-4,-3) if d==-4 else (min(5,d+1),)):nxt[e]=dst.merge(nxt.get(e,0),v)
        dst.merge.cache_clear()
        src,roots=dst.collect(nxt)
        assert bool(roots)==(i>57)
    print('fixed physical suffix: no five-hop extension through column 57 at any price')
if __name__=='__main__':
    import sys
    if sys.argv[1:2]==['extension']:extension(int(sys.argv[2]))
    else:check(*map(int,sys.argv[1:]))
