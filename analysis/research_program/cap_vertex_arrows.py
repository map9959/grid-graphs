"""Alternative slit transducer: orient each individual forced edge and bill marked sinks."""
from functools import lru_cache
from itertools import product
from .finite_cap_language import extend


def moves(st,v,drop,last=False):
    m,above,used,part,flags,first=st
    if v&(m<<1|m>>1):return
    old=(m>>1)&7;new=(v>>1)&7;vert=old|new
    h=m<<1|m>>1;bare=14&~m
    iso=bare&~(v|above|h)
    cost=iso.bit_count()+int(bool(iso&4))+((bare&10)&((m<<1&m>>1)|(above&v))).bit_count()
    cost+=2*int(bool(v&4&~(m|(v<<1)|(v>>1))))+int(bool(v&4&((v<<1)^(v>>1))))
    for down in range(8):
        if down&~vert or down&used or last and down:continue
        if first and down!=(2 if drop else 0):continue
        unassigned=7&~(down|used)
        if not first and unassigned&~old&~(iso>>1):continue
        sinks=0 if first else unassigned&old
        # Physical proof uses a forest even inside the strip. Its one
        # waived terminal cannot share a tree with a charged nonterminal sink.
        p=[*part,3,4,5];tag=[*flags,0,0,0]
        def rt(a):
            while p[a]!=a:a=p[a]
            return a
        def insert(a,b):
            a,b=rt(a),rt(b)
            if a==b:return False
            p[a]=b;tag[b]|=tag[a];return tag[b]!=3
        for k in range(3):
            if sinks>>k&1:tag[rt(k)]|=2
        if 3 in tag:continue
        if not all(insert(i,i+3) for i in range(3) if vert>>i&1):continue
        if not all(insert(i+3,i+4) for i in range(2) if (new>>i)&3):continue
        rr=[rt(3+i) for i in range(3)]
        pp=tuple(rr.index(r) for r in rr);ff=tuple(tag[r] if pp[i]==i else 0 for i,r in enumerate(rr))
        # Four horizontal bonds, in geographical order, including slits.
        dirs=[(0,1) if v>>i&3 else (-1,) for i in range(4)]
        for ds in product(*dirs):
            busy=vert^down
            for i,d in enumerate(ds):
                if d<0:continue
                src=i-1 if d else i
                if 0<=src<3:
                    if busy>>src&1:break
                    busy|=1<<src
            else:
                l=(v&3)+4*(ds[0]==1);r=(v>>3)+4*(ds[3]==1)
                yield l,r,(v,m&14,busy,pp,ff,False),cost+2*sinks.bit_count()


@lru_cache(None)
def transfer(edge,drop):
    # A first-row terminal is special: choosing its edge down waives
    # it. Treat the other two virtual sites as already oriented inward.
    start=(4,0,5,(0,0,0),(int(drop),0,0),True)
    ls=[start];ids={start:0};arcs=[];end={}
    for i,s in enumerate(ls):
        opts=set()
        for v in range(32):
            if edge=='L' and v&3 or edge=='R' and v&24:continue
            for l,r,t,z in moves(s,v,drop):
                if t not in ids:ids[t]=len(ls);ls.append(t)
                opts.add((l,r,ids[t],z))
        arcs.append(sorted(opts))
        for _,_,_,z in moves(s,0,drop,last=True):
            e=z+(14&~s[0]).bit_count()+int(not(s[0]&4))
            end[i]=min(end.get(i,e),e)
    return arcs,end


def extend_vertex(options,edge,limit):
    return extend(options,edge,limit,local=transfer)
