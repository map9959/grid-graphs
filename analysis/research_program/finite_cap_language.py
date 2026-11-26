"""Finite-width, unbounded-height cap relaxation using directed slit words.

Charge an extra tree where its unique outward orientation stops, rather
than dropping its price whenever it crosses an auxiliary window border.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import product


def step(s,v,L,R):
    m,up,part,tags=s
    if v&((m<<1)|(m>>1)):return
    p=[*part,3,4,5];tag=[*tags,*[v>>(i+1)&1 for i in range(3)]]
    def root(i):
        while p[i]!=i:i=p[i]
        return i
    def join(i,j):
        a,b=root(i),root(j)
        if a==b or tag[a]==tag[b]==2:return False
        t,u=tag[a],tag[b]
        p[a]=b;tag[b]=2 if 2 in (t,u) else max(t,u);return True
    for i in range(3):
        if (v|m)>>(i+1)&1 and not join(i,3+i):return
        if i and v>>i&3 and not join(2+i,3+i):return
    for a,d,i in [(v&3,L,3),(v>>3,R,5)]:
        if a:
            x=root(i);out=d==(0 if i==3 else 1)
            if out and tag[x]==2:return
            tag[x]=2 if out else max(1,tag[x])
    # The same colored bill as pitch_endpoint_tariff.rs. In the
    # noncentral overlap term only *blank* sites are charged.
    bare=14&~m;lat=m<<1|m>>1
    iso=bare&~(v|up|lat)
    cost=iso.bit_count()+(iso&4).bit_count()+(bare&10&((m<<1&m>>1)|(up&v))).bit_count()
    hor=v<<1|v>>1
    cost+=2*int(bool(v&4&~(hor|m)))+(v&4&((v<<1)^(v>>1))).bit_count()
    rs=[root(i) for i in range(3,6)];gone=[tag[i] for i in range(3) if p[i]==i and i not in rs]
    if 3 in gone:return
    cost+=2*gone.count(1)
    pp=tuple(rs.index(i) for i in rs)
    return (v,m&~v&14,pp,tuple(tag[r] if pp[i]==i else 0 for i,r in enumerate(rs))),cost


@lru_cache(None)
def transfer(edge,drop):
    ini=(4,0,(0,0,0),(3 if drop else 2,0,0));ls=[ini];ids={ini:0};arcs=[];ends={}
    for u,s in enumerate(ls):
        row=[];m=s[0]
        end=step(s,0,0,0)
        if end is not None:
            (_,_,_,tags),z=end
            if 3 not in tags:ends[u]=z+(14&~m).bit_count()+int(not(m&4))+2*tags.count(1)
        forbid=(m<<1)|(m>>1)|(3 if edge=='L' else 24 if edge=='R' else 0)
        for v in range(32):
            if v&forbid:continue
            a=v&3;b=v>>3
            for L,R in product(range(2 if a else 1),range(2 if b else 1)):
                ans=step(s,v,L,R)
                if ans is None:continue
                t,z=ans
                if t not in ids:ids[t]=len(ls);ls.append(t)
                row.append((a+4*L,b+4*R,ids[t],z))
        arcs.append(row)
    return arcs,ends


def reduce_nfa(rows,final,limit):
    # Discard dead NFA states *before* determinization.
    pred=[set() for _ in rows]
    for u,row in enumerate(rows):
        for vs in row.values():
            for v in vs:pred[v].add(u)
    live=set(final);queue=list(live)
    for v in queue:
        for u in pred[v]-live:live.add(u);queue.append(u)
    if 0 not in live:return [{}],set()
    ls=[frozenset({0})];ids={ls[0]:0};out=[];end=set()
    for i,s in enumerate(ls):
        if s&final:end.add(i)
        opts=defaultdict(set)
        for u in s:
            for a,vs in rows[u].items():opts[a]|=vs&live
        tab={}
        for a,v in opts.items():
            if not v:continue
            t=frozenset(v)
            if t not in ids:
                assert len(ids)<limit,('subset cap',len(rows),limit)
                ids[t]=len(ls);ls.append(t)
            tab[a]=ids[t]
        out.append(tab)
    colors=[int(i in end) for i in range(len(out))]
    while True:
        ix={};c=[ix.setdefault((i in end,tuple(sorted((a,colors[v]) for a,v in row.items()))),len(ix))
                 for i,row in enumerate(out)]
        if c==colors:break
        colors=c
    ans=[{} for _ in ix]
    for i,row in enumerate(out):ans[c[i]]={a:c[v] for a,v in row.items()}
    return ans,{c[i] for i in end}


def extend(options,edge,limit,local=transfer):
    # Each option is (input DFA, available local budget, waiver flag).
    starts=[(k,0,0,z) for k,(_,z,_) in enumerate(options)]
    ls=[None,*starts];idx={t:i for i,t in enumerate(ls)};rows=[];end=set()
    for i,t in enumerate(ls):
        cur=defaultdict(set);rows.append(cur)
        for k,a,u,z in starts if t is None else [t]:
            (dfa,accept),_,drop=options[k];arcs,finish=local(edge,drop)
            if a in accept and finish.get(u,10**6)<=z:end.add(i)
            for l,r,v,c in arcs[u]:
                b=dfa[a].get(l)
                if b is None or z<c:continue
                dest=k,b,v,z-c
                if dest not in idx:
                    assert len(ls)<limit*3,('product cap',len(ls))
                    idx[dest]=len(ls);ls.append(dest)
                cur[r].add(idx[dest])
    return reduce_nfa(rows,end,limit)

