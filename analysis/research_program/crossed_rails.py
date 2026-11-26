"""Four nonparallel rail sectors. Exact width-free transfer at primal period 3."""
from collections import Counter
from functools import lru_cache
from heapq import heappop,heappush
from itertools import product

from .period_nine import budgets

N=6
P=3
ALL=(1<<N)-1


def shift(x):
    return (x>>1)|((x&1)<<(N-1))


@lru_cache(None)
def moves(occ):
    free=ALL^occ
    v=free
    out=[]
    while True:
        h=shift(free^v)
        if not v&h:out.append((v,v|h))
        if not v:break
        v=(v-1)&free
    return out


def state(tile,reflect,last):
    def at(i,j):
        x,y=tile[i%N,(last-j if reflect else j)%N]
        return (x,-y if reflect else y)
    def cross(d,step):
        return sum(1<<c for c in range(N) if at(c+d,c)==step)
    v=cross(-1,(1,0))
    return v|shift(cross(-1,(0,-1))), (v|cross(-2,(1,0)))^0b101010,0


@lru_cache(None)
def cost(p,n):
    degs=[sum((m>>(j%N))&1 for m,j in ((p,c),(p,c+1),(n,c),(n,c-1)))
          for c in range(0,N,2)]
    return sum(d-1 for d in degs if d<4)


def distances(start,exits,cap):
    dist={start:0};q=[(0,start)]
    while q:
        k,s=heappop(q)
        if dist[s]!=k:continue
        occ,prev,ph=s
        for v,o in moves(occ):
            for w,e in moves(o):
                nxt=(v|w)^0b101010
                c=cost(prev,nxt)
                assert c>=0
                z=k+c;t=e,nxt,(ph+1)%P
                if z<=cap and z<dist.get(t,cap+1):
                    dist[t]=z;heappush(q,(z,t))
    return [dist.get(t,cap+1) for t in exits]


def census(a=4,b=4):
    rows=budgets(P,0,a,b)
    last=8
    cap=2*P
    mat=[]
    for reflected in [False,True]:
        cuts=[state(d,reflected,last) for _,d,_ in rows]
        ds={s:distances(s,cuts,cap) for s in set(cuts)}
        mat.append([ds[s] for s in cuts])
    # Normal increases downward. NW: top -> left, SE: right -> bottom.
    # After reflection NE: top -> right and SW: left -> bottom.
    cand=[[i for i,d,c in rows if c[s]<1000] for s in range(4)]
    best=10000;wins=[]
    for top,right,bottom,left in product(*cand):
        arms=sum(rows[i][2][s] for s,i in enumerate((top,right,bottom,left)))
        joins=[mat[0][top][left],mat[1][top][right],
               mat[0][right][bottom],mat[1][left][bottom]]
        total=2*arms+sum(joins)
        best=min(best,total)
        if total<=cap:wins.append(((top,right,bottom,left),arms,joins))
    print("split",a,b,"period",P,"sectors tested",list(map(len,cand)),
          "loss budget",cap,"lower bound",best,"survivors",len(wins))
    if wins: print("first survivor",wins[0])
    return wins


def cut_data(d,ref,last,p):
    n=2*p
    def get(r,c):
        x,y=d[r%n,(last-c if ref else c)%n]
        return x, -y if ref else y
    def full(r,c):
        return all(not (2*r+x+get(2*r+x,2*c+y)[0])%2 for x,y in ((1,0),(-1,0),(0,1),(0,-1)))
    occ=sum(get(c-1,c) in ((1,0),(0,-1)) for c in range(n))
    rails=set()
    for i,j in product(range(p),repeat=2):
        if full(i,j):
            x,y=get(2*i,2*j)
            rails.add((bool(y),i if y else j))
    # Oriented rightward current across the cut from primal d<=0 to d>=1.
    ff=u=0
    for di,j in product((0,1),range(p)):
        i=j+di
        x,y=get(2*i,2*j)
        sign=int(di+x-y>=1)-int(di>=1)
        if sign:
            if not full(i+x,j+y):u+=sign
            elif full(i,j):ff+=sign
    return occ,frozenset(rails),ff,u


def flux_census(p=9,r=0,a=4,b=4,return_tables=False):
    rows=budgets(p,r,a,b)
    mat=[]
    blocked=1000
    for reflected in (False,True):
        data=[cut_data(d,reflected,8+6*r,p) for _,d,_ in rows]
        mat.append([[blocked if occ!=occ2 else
                     max(0,(len(A^B)+f-g+1)//2+u-v)
                     for occ2,B,g,v in data] for occ,A,f,u in data])
    cand=[[i for i,_,c in rows if c[s]<=p] for s in range(4)]
    if return_tables:return rows,mat,cand
    # Independent left and right sector choices once top and bottom are fixed.
    best=blocked; witness=None;count=0
    for t,bm in product(cand[0],cand[2]):
        l=min((2*rows[i][2][3]+mat[0][t][i]+mat[1][i][bm],i) for i in cand[3])
        h=min((2*rows[i][2][1]+mat[1][t][i]+mat[0][i][bm],i) for i in cand[1])
        val=2*(rows[t][2][0]+rows[bm][2][2])+l[0]+h[0]
        if val<best:best=val;witness=(t,h[1],bm,l[1])
        count+=val<=2*p
    print("flux relaxation period",p,"residue",r,"lower bound",best,
          "budget",2*p,"eligible top/bottom pairs",count,"minimizer",witness,flush=True)
    return best


def two_corner_bound(r=0):
    """Bound each corner independently, allocating each side-arm cost twice."""
    rows,mats,opts=flux_census(r=r,return_tables=True)
    for ref,s,t in ((0,0,3),(1,0,1),(0,1,2),(1,3,2)):
        counts=Counter(rows[i][2][s]+rows[j][2][t]+mats[ref][i][j] for i,j in product(opts[s],opts[t]))
        print("corner",s,t,"lower bound <=4:",{c:n for c,n in counts.items() if c<=4})


def rotational(r,run=True):
    """Four sectors related by quarter turns about the square center."""
    import subprocess
    from pathlib import Path
    rows=budgets(9,r); last=8+6*r
    key=lambda d:tuple(d[i,j] for i,j in product(range(18),repeat=2))
    ids={key(d):i for i,d,_ in rows}
    def rotate(d):
        return {(j,(last-i)%18):(y,-x) for (i,j),(x,y) in d.items()}
    tasks={}
    for i,d,_ in rows:
        sec=[i]
        for t in range(3):
            d=rotate(d);sec.append(ids[key(d)])
        arm=sum(rows[j][2][s] for s,j in enumerate(sec))
        q=(18-2*arm)//4
        if q<0:continue
        t,l=sec[0],sec[-1]
        low,high=rows[t][1],rows[l][1]
        from .period_nine import state as start
        sl,sr=start(low),start(high,True)
        if sl[0].bit_count()+sr[0].bit_count()!=18:continue
        # Simultaneous translation of both backgrounds changes neither
        # the cost nor existence of a cylinder join. Phase-zero ends can
        # be padded by homogeneous slices.
        canon=min(tuple(key({(i,j):d[(i+u)%18,(j+v)%18] for i,j in d})
                        for d in (low,high)) for u,v in product(range(0,18,2),repeat=2))
        tasks.setdefault((canon,q),[]).append((sl,sr,sec))
    print("quarter-turn templates",sum(map(len,tasks.values())),"translation orbits",len(tasks),flush=True)
    if not run:return tasks
    binary=Path(__file__).resolve().parents[2]/'target/release/diagonal_nine'
    passed=[]
    for (_,q),group in tasks.items():
        sl,sr,sec=group[0]
        text=" ".join(map(str,[*sl,*sr,q,sec[0],sec[-1]]))
        s=subprocess.run([binary,'--sector'],input=text,text=True,capture_output=True,check=True)
        if int(s.stdout.split()[-1])<=q:passed.extend(item[2] for item in group)
    print("quarter-turn survivors",len(passed),"first",passed[:1],flush=True)
    return passed


if __name__=="__main__":
    census()
    for r in range(3):
        flux_census(r=r)
