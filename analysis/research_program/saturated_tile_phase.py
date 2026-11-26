"""Bulk phase rigidity of adjacent saturated one-gap tiles on the exceptional tail."""
from itertools import combinations,product
from pathlib import Path
import heapq,subprocess,sys
from .defect_window import table,window

PHASE=(7,56,448,73,146,292)  # three row words and three column words
ROW={9,18,36,66,72,73,129,132,144,146,258,288,292}
COL={3,6,7,12,24,33,48,56,96,192,264,384,448}

def axis_clauses(f,bit,n,domain=None):
    """Necessary throughout a rectangular deep bulk; either type of gap."""
    from .tight_corner_sat import cover
    inds=list(range(14,n-14,3));top=f.nv;axis=top+1
    row={i:axis+1+h for h,i in enumerate(inds)}
    col={j:axis+1+len(inds)+h for h,j in enumerate(inds)}
    forbidden=[cover(tuple(m not in words for m in range(512))) for words in (ROW,COL)]
    for rv in row.values():f.append([-rv,axis])
    for cv in col.values():f.append([-cv,-axis])
    for i,j in product(inds,repeat=2):
        if domain is not None and not all((i+a,j+b) in domain for a,b in product((-1,0,1),repeat=2)):continue
        vs=[bit(i+a,j+b) for a,b in product((-1,0,1),repeat=2)]
        for flag,nb,terms in zip((row[i],col[j]),((1,7),(3,5)),forbidden):
            for k in nb:f.append([-vs[4],-vs[k],flag])
            for mask,v in terms:
                f.append([-flag]+[(-z if v>>k&1 else z) for k,z in enumerate(vs) if mask>>k&1])

def relation(f,tiles):
    """Exact two-tile projection of the local relaxation; certify exhaustion."""
    from pysat.solvers import Solver
    graph={}
    with Solver(name='cadical195',bootstrap_with=f.clauses) as solver:
        while solver.solve():
            model=set(solver.get_model())
            a,b=(sum((z in model)<<k for k,z in enumerate(tile)) for tile in tiles)
            assert 1<=a.bit_count()<=3 and 1<=b.bit_count()<=3
            graph.setdefault(a,set()).add(b)
            nogood=[-z if z in model else z for tile in tiles for z in tile]
            f.append(nogood);solver.add_clause(nogood)
    return graph

def projection(f,tiles,vertical):
    graph=relation(f,tiles)
    predecessor={b:{a for a,vs in graph.items() if b in vs} for vs in graph.values() for b in vs}
    forward,back=(7,448) if vertical else (73,292)
    assert graph[forward]=={forward} and predecessor[back]=={back}
    assert {a for a in graph if a.bit_count()==3}==set(PHASE)
    assert all(a==b for a,bs in graph.items() for b in bs if a.bit_count()==b.bit_count()==3)
    costs=[]
    for source in PHASE:
        d={source:0};todo=[(0,source)]
        while todo:
            cost,u=heapq.heappop(todo)
            if cost!=d[u]:continue
            for v in graph.get(u,()):
                new=cost+3-v.bit_count()
                if new<d.get(v,float('inf')):
                    d[v]=new;heapq.heappush(todo,(new,v))
        costs.append([d.get(v,'inf') for v in PHASE])
    print(sum(map(len,graph.values())),'allowed adjacent pairs; minimum path deficits',costs)
    p=graph
    for t in range(1,100):
        q={a:set().union(*(graph.get(v,()) for v in bs)) for a,bs in p.items()}
        if q==p:break
        p=q
    else:raise AssertionError('no stabilization')
    print('tile relation stabilizes at distance',t,'ordered endpoint masks',sum(map(len,p.values())))
    costs={(u,v):3-v.bit_count() for u,vs in graph.items() for v in vs}
    for t in range(1,100):
        new={}
        for (u,v),c in costs.items():
            for w in graph.get(v,()):
                cw=c+3-w.bit_count();key=u,w
                if cw<new.get(key,10000):new[key]=cw
        if costs.keys()==new.keys():
            slope={k:new[k]-c for k,c in costs.items()}
            # Induction: every candidate line is at least the target at
            # the base and has no smaller slope; one coincides forever.
            equal=set();ok=True
            for (u,v),c in costs.items():
                for w in graph.get(v,()):
                    k=u,w
                    if slope[u,v]<slope[k]:ok=False
                    if slope[u,v]==slope[k] and c+3-w.bit_count()==new[k]:equal.add(k)
            if ok and equal==costs.keys():break
        costs=new
    else:raise AssertionError('no affine recurrence')
    from collections import Counter
    print('exact affine minimum deficits from length',t,'slopes',dict(Counter(slope.values())))
    print('linear-cost endpoints (first,last,intercept):',
          sorted((u,v,costs[u,v]-t) for (u,v),m in slope.items() if m==1))
    return graph,costs,slope,t

def prove():
    n=119;x=40;tables=table(n);relations=[]
    halo=6 if '--cross' in sys.argv else 2
    for di,dj in ((0,1),(1,0)):
        dom=set(product(range(x-halo,x+3+halo+3*di),range(x-halo,x+3+halo+3*dj)))
        def emit(f,bit,flags):
            tiles=[[bit(x+i+h*3*di,x+j+h*3*dj) for i,j in product(range(3),repeat=2)] for h in (0,1)]
            project='--project' in sys.argv or halo==6
            if project:relations.append(projection(f,tiles,di)[0])
            else:
                for tile in tiles:
                    f.extend([list(c) for c in combinations(tile,7)]) # at least three
                for m in PHASE:
                    f.append([(-v if m>>k&1 else v) for tile in tiles for k,v in enumerate(tile)])
            stem=Path(f'target/saturated_tile_phase_{di}_{dj}'+('_projection' if project else '')+('_cross' if halo==6 else ''))
            cnf=stem.with_suffix('.cnf');proof=stem.with_suffix('.drat')
            f.to_file(str(cnf))
            with stem.with_suffix('.log').open('wb') as log:
                assert subprocess.run(['target/cadical/build/cadical',str(cnf),str(proof)],stdout=log).returncode==20
            check=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(proof)],capture_output=True,check=True)
            assert b's VERIFIED' in check.stdout
            print((di,dj),'projection exhaustive' if project else 'at least three in each and not identical straight triples',': s VERIFIED')
        window(n,'rim',1,tables,want=False,domain=dom,emit=emit,turn_domain=set())
    if halo==6:
        reach=[]
        for g,seeds in zip(relations,((18,144,146),(24,48,56))):
            rev={b:{a for a in g if b in g[a]} for vs in g.values() for b in vs}
            r=set()
            for d in (g,rev):
                q=set(seeds)
                while (more:=q.union(*(d.get(v,()) for v in q)))!=q:q=more
                r.update(q)
            reach.append(r)
            # These are exactly the possible masks containing a center
            # and a vertical (respectively horizontal) neighbor.
            neighbors=130 if seeds[0]==18 else 40
            assert {m for m in set(g)|set(rev) if m&16 and m&neighbors}==set(seeds)
            # Any path flanked by the same middle stripe stays inside
            # this SCC. Its tiles are all subsets of that stripe.
            phase=seeds[-1];closures=[]
            for d in (g,rev):
                q={phase}
                while (more:=q.union(*(d.get(v,()) for v in q)))!=q:q=more
                closures.append(q)
            assert closures[0]&closures[1]==set(seeds)
            assert all(m&~phase==0 for m in seeds)
        assert reach==[ROW,COL] and ROW.isdisjoint(COL)
        print('reachable anywhere along middle-column tile row:',sorted(reach[0]))
        print('reachable anywhere along middle-row tile column:',sorted(reach[1]))
        print('disjoint: perpendicular central phases cannot coexist anywhere in the deep bulk')

if __name__=='__main__':prove()
