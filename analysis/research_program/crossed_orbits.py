"""Reuse certified seam bounds across independently chosen period-nine sectors."""
from collections import Counter
from itertools import product
from .crossed_rails import flux_census


def census(r=0,return_tables=False):
    rows,mat,opt=flux_census(r=r,return_tables=True)
    last=8+6*r
    key=lambda d:bytes((x+1)*3+y+1 for x,y in d)
    sites=list(product(range(18),repeat=2))
    ids={key([d[z] for z in sites]):i for i,d,_ in rows}
    tr=[]; refl=[]; turn=[]
    for i,d,_ in rows:
        tr.append([ids[key([d[(u+a)%18,(v+b)%18] for u,v in sites])]
                   for a,b in product(range(0,18,2),repeat=2)])
        refl.append(ids[key([(x,-y) for u,v in sites for x,y in [d[u,(last-v)%18]]])])
        turn.append(ids[key([(-y,x) for u,v in sites for x,y in [d[v,(last-u)%18]]])])
    def orbit(i,j):
        return min(zip(tr[i],tr[j]))
    certified=set()
    for t,_,_ in rows:
        l=turn[t];bm=turn[l];h=turn[bm]
        arm=sum(rows[i][2][s] for s,i in enumerate((t,h,bm,l)))
        if arm==0 and mat[0][t][l]<1000:
            certified.add(orbit(t,l))
    assert len(certified)==24
    mods=0
    for ds in range(2):
        for i,j in product(range(len(rows)),repeat=2):
            if mat[ds][i][j]>=5:continue
            pair=(refl[i],refl[j]) if ds else (i,j)
            if orbit(*pair) in certified:
                mat[ds][i][j]=5
                mods+=1
    hist=Counter()
    for t,bm in product(opt[0],opt[2]):
        g=2*(rows[t][2][0]+rows[bm][2][2])
        if g>18:continue
        halves=[]
        for s in (3,1):
            counts=Counter()
            for i in opt[s]:
                v=2*rows[i][2][s]+mat[int(s==1)][t][i]+mat[int(s==3)][i][bm]
                if g+v<=18:counts[v]+=1
            halves.append(counts)
        for v,n in halves[0].items():
            for w,m in halves[1].items():
                if g+v+w<=18:hist[g+v+w]+=n*m
    print("residue",r,"certified directed seam orbits",len(certified),"tightened entries",mods,
          "remaining assignments",sum(hist.values()),"by relaxed loss",dict(sorted(hist.items())),flush=True)
    if return_tables:return rows,mat,opt,tr,refl
    return hist


if __name__=='__main__':
    for r in range(3):census(r)
