"""Length-free two-tile-high clean bridges joining the north corner/exit boxes."""
from itertools import product
import sys
from .tile_family_lp import projected,typ
from .saturated_tile_phase import ROW

def install(marks,rowflag,fresh,append):
    # Reference 329 labels. Both exterior seam columns stay fixed relative
    # to their corners; the interior columns stay fixed relative to the exit.
    B=projected(3,5)
    lengths='--lengths' in sys.argv
    if lengths:
        # For n=329+42t, L+R=(n-179)/3=50+14t. Select
        # representatives in [6, ...] common to every transverse row.
        start=next((int(s[6:]) for s in sys.argv if s.startswith('--min=')),6)
        end=start+20
        lens=list(range(start,end+14))
        choose=[[fresh() for _ in lens] for _ in (0,1)]
        for ls in choose:append(ls)
        fixed=next((tuple(map(int,s[8:].split(','))) for s in sys.argv if s.startswith('--fixed=')),None)
        if fixed:
            assert len(fixed)==2 and all(k in lens for k in fixed)
            for side,k in enumerate(fixed):append([choose[side][lens.index(k)]])
        for i,a in enumerate(lens):
            for j,b in enumerate(lens):
                if (a+b-50)%14:append([-choose[0][i],-choose[1][j]])
    def flip(m):return sum((m>>(3*i+j)&1)<<(3*i+2-j) for i,j in product(range(3),repeat=2))
    for r in range(20):
        origin=1+3*r
        if origin+5>=65:continue
        for L,R,j,k,reverse in ((0,2,52,127,False),(2,1,199,274,True)):
            ws=B[typ(r,38),6]
            if reverse:ws=[tuple(flip(w[i]) for i in (1,0,3,2)) for w in ws]
            use=[h for h in (0,1) if origin+1+3*h>=14]
            ws=[w for w in ws if all(not(m&16 and m&40) for h in use for m in w[2*h:2*h+2])]
            edges={((a,c),(b,d)) for a,b,c,d in ws}
            nodes=sorted({p for edge in edges for p in edge})
            ends=[]
            for block,y in ((L,j),(R,k)):
                vs={}
                for node in nodes:
                    z=fresh();vs[node]=z
                    for h,m in enumerate(node):
                        for i,jj in product(range(3),repeat=2):
                            x=marks[block][origin+3*h+i,y+jj]
                            append([-z,x if m>>(3*i+jj)&1 else -x])
                append(list(vs.values()));ends.append(vs)
            for act in product((False,True),repeat=len(use)):
                guard=[rowflag(origin+1+3*h)*(-1 if v else 1) for h,v in zip(use,act)]
                def legal(p):
                    return all((p[h] in ROW if flag else not(p[h]&16 and p[h]&130)) for h,flag in zip(use,act))
                adj={p:set() for p in nodes}
                for a,b in edges:
                    if legal(a) and legal(b):adj[a].add(b)
                if lengths:
                    rel={a:{a} for a in nodes};saved={};side=int(reverse)
                    for kpow in range(end+15):
                        if kpow>=start:saved[kpow]=rel
                        rel={a:set().union(*(adj[b] for b in rel[a])) for a in nodes}
                    assert saved[end]==saved[end+14],(r,reverse,act)
                    for a in nodes:
                        # Group identical support lists. The allowed
                        # length selector implies the corresponding list.
                        records={}
                        for t,kpow in enumerate(lens):
                            rec=tuple(sorted(saved[kpow][a]));records.setdefault(rec,[]).append(t)
                        for rec,idx in records.items():
                            clause=[*guard,-ends[0][a],*[ends[1][p] for p in rec]]
                            if len(idx)==len(lens):append(clause)
                            else:
                                for t in idx:append([-choose[side][t],*clause])
                    continue
                for a in nodes:
                    seen=set(adj[a]);queue=list(seen)
                    for b in queue:
                        for c in adj[b]-seen:seen.add(c);queue.append(c)
                    append([*guard,-ends[0][a],*[ends[1][p] for p in sorted(seen)]])
