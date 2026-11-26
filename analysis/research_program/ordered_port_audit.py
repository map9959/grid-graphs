"""Independent physical graph check of ordered port identity and displacement."""
from .ordered_ports import relation,glue
from .joined_arm_budget import layout,row,spectrum,physical

def replay():
    k,H,_=layout(0);s=k-4*H//3
    bits,get=spectrum(7,4,1,True,0,True,s,True)
    cap=get((bits&-bits).bit_length()-1)
    w=list(zip(*[(*a,*b) for a,b in zip(cap,zip(*(row(k,q)[1] for q in reversed(range(H)))))]))
    start=k-len(w);N=3*k
    assert physical(list(zip(*w)),start,k,1,True,require_roots=True)[1]==0
    X={(3*i+b//3,3*j+b%3) for i,col in enumerate(w,start) for j,m in enumerate(col)
       for b in range(9) if m>>b&1}
    p={};rooted={}
    def rt(u):
        while p[u]!=u:p[u]=p[p[u]];u=p[u]
        return u
    def join(u,v):
        a,b=rt(u),rt(v);assert a!=b and not(rooted[a] and rooted[b])
        p[a]=b;rooted[b]|=rooted[a]
    def cut(i):
        c=3*(i+1);ls=[]
        for y in range(N):
            if (c-1,y) in X and (c,y) in X:ls.append((y,0,c-1))
            elif (c-2,y) in X and (c-1,y) not in X and (c,y) in X:ls.append((y,1,c-2))
            elif (c-1,y) in X and (c,y) not in X and (c+1,y) in X:ls.append((y,2,c-1))
        names={};part=[]
        for y,_,x in ls:
            u=rt((x,y));part.append(0 if rooted[u] else names.setdefault(u,len(names)+1))
        return (tuple(3*(y%3)+c for y,c,x in ls),tuple(part)),tuple(y for y,_,_ in ls),tuple(names)
    t=relation(1,7,phase=-4,offset=-4,ends=True,lineage=True,drift=8)
    left=((),());ys=old=();n=replaced=0
    for i in range(start,k):
        for u in X:
            if u[0]//3!=i:continue
            x,y=u;p[u]=u;rooted[u]=min(x,y,N-1-x,N-1-y)==1
        for u in X:
            if u[0]//3!=i:continue
            for dx,dy in ((-1,0),(0,-1)):
                v=u[0]+dx,u[1]+dy
                if v not in X:v=v[0]+dx,v[1]+dy
                if v in X:join(u,v)
        right,new,ids=cut(i)
        if i>start and i<=k-8 and len(ys)==len(new)==2:
            j=i-start
            key=(*left,(w[j-1][0],w[j][0],w[j-1][-1],w[j][-1]))
            dest=(*right,(w[j][0],w[j+1][0],w[j][-1],w[j+1][-1]))
            heirs=tuple(0 if rooted[rt(u)] else ids.index(rt(u))+1 for u in old)
            drift=tuple(max(-8,min(8,b-a)) for a,b in zip(ys,new))
            loss=sum(3-m.bit_count() for m in w[j])
            assert t[key,dest,heirs,drift]>=loss
            n+=1;replaced+=sum(v==0 for v in heirs)
        left,ys,old=right,new,ids
    assert n>0 and replaced>0
    print('physical rooted-region replay:',n,'two-hop bulk columns;',replaced,'incoming classes grounded')

def east():
    assert glue(2,1,(7,25),(1,0),2,True)==((0,),(0,))
    assert glue(2,1,(7,25),(0,1),2,True) is None  # same counts, opposite order
    assert glue(2,1,(29,),(1,2),2,True)==((1,),(1,1))
    assert glue(2,1,(29,),(1,1),2,True) is None  # same order, changed partition
    assert glue(1,0,(7,),(1,),2,True)==((),(0,))
    for a in (1,2):
        rel=relation(a,7,phase=-4,offset=-4,ends=True,lineage=True,drift=8)
        assert all(p[0] and q[0] and dy[0]>=0 and 4*(loss-3)<=3*dy[0]
                   for (p,q,heir,dy),loss in rel.items())
        assert all(heir.count(0)==1 and len(set(q[1])-{0}-set(heir))==1
                   for (p,q,heir,dy),loss in rel.items() if loss>3)
        # This equality uses the fully ordered physical seam, not just
        # whether it exposes some unrooted component.
        hot=[(p,q,h,d) for (p,q,h,d),loss in rel.items() if loss==6 and
             p[2]==q[2]==(6,6,192,192) and p[1]==q[1]==(1,0)]
        assert len(hot)==3 and all(d==(4,4) and h==(0,) for p,q,h,d in hot)
        print('axis',a,'southward speed on the three recurrent expensive transitions: 4 and 4 sites')
        # Isolate lies in the bulk. Leave all incoming component states
        # free; propagate through its fixed offsets and one clean column.
        st=None
        for offset in range(5,-5,-1):
            t=relation(a,7,phase=4 if offset==5 else -4 if offset==-4 else None,offset=offset,ends=True)
            st={q for p,q in t if st is None or p in st}
        assert len(st)==7 and all(p[0] in ((0,),(0,0)) and p[2]==(6,6,73,73) for p in st)
        continuing=[(p,q,h,d,v) for (p,q,h,d),v in rel.items() if p in st]
        assert {p for p,_,_,_,_ in continuing}==st
        assert all(p==q and not any(d) and v==3 for p,q,h,d,v in continuing)
        for r in range(32,39):
            tab=relation(a,r,phase=-4,offset=-4,ends=True)
            st={q for p,q in tab if p in st}
        assert not st
        print('bulk-isolate corridor: seven stationary profiles, disjoint from the east closure cycle')
if __name__=='__main__':east();replay()
