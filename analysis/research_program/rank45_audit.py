"""Independent contracted-graph check of the three- and four-class refill catalogues."""
from collections import Counter,defaultdict
from itertools import combinations,product
from .four_square import masks4
from .rank44_faces import table,parts


def components(vertices,edges):
    adj={u:set() for u in vertices}
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    left=set(vertices);ans={}
    while left:
        root=left.pop();stack=[root]
        while stack:
            u=stack.pop();ans[u]=root
            for v in adj[u]&left:left.remove(v);stack.append(v)
    return ans


def audit(C=3):
    cell=range(16);corners=(0,3,12,15);inside={5,6,9,10}
    border=set(cell)-inside;lib=masks4()
    pairs=[(u,v) for u,v in combinations(cell,2) if
           abs(u//4-v//4)+abs(u%4-v%4)==1]
    partitions={tuple(sorted(tuple(i for i,d in enumerate(w) if d==c)
                      for c in set(w))) for w in product(range(C),repeat=4)}
    assert len(partitions)=={3:14,4:15}[C]
    valid=defaultdict(list)
    for m in lib:
        sk=m & ~sum(1<<u for u in inside)
        base=[(u,v) for u,v in pairs if sk&(1<<u|1<<v)]
        extra=[(u,v) for u,v in pairs if m&(1<<u|1<<v) and (u,v) not in base]
        for blocks in partitions:
            word=tuple(next(c for c,g in enumerate(blocks) if i in g) for i in range(4))
            ties=[(corners[g[0]],corners[i]) for g in blocks for i in g[1:]]
            first=components(cell,base+ties)
            if len({first[i] for i in corners})!=len(blocks):continue
            last=components(cell,base+ties+extra)
            if len(set(first.values()))-len(set(last.values()))!=len(extra):continue
            join=len(blocks)-len({last[i] for i in corners})
            relation=frozenset((a,b) for a,b in combinations(sorted(border),2) if last[a]==last[b])
            valid[sk,word].append((m,join,relation,(m^sk).bit_count()))
    if C==4:
        ranks=Counter(r for states in valid.values() for _,r,_,_ in states)
        print('four-class raw acyclic states by join rank',sorted(ranks.items()))
    for j in range(C):
        expected={}
        for (_,word),states in valid.items():
            states=[s for s in states if s[1]<=j]
            for m,r,p,n in states:
                if any(nn>n and pp<=p for _,_,pp,nn in states):continue
                expected[m,word]=r
        assert expected==table(C,j)
        for (m,q),r in expected.items():
            for g,im in enumerate(lib[m][1]):assert expected[im,parts(q,g)]==r
        print(f'C={C} join cap',j,'verified states by exact join rank',sorted(Counter(expected.values()).items()))


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--components',choices=(3,4),type=int,default=3)
    audit(p.parse_args().components)
