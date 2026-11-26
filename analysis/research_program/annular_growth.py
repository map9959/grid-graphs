"""Exact maximum after opening the old perimeter and inserting an L or annulus."""
from itertools import product
from pathlib import Path
import subprocess,sys

def graph(n,q,a,b,pump=False,two_gap=False,bridge=None):
    N=n+3*q;lo,hi=a+1,a+n-2;le,ri=b+1,b+n-2
    rows=[range(lo),range(lo,hi+1),range(hi+1,N)]
    cols=[range(le),range(le,ri+1),range(ri+1,N)]
    # Clockwise sweep. Choose a thin interface for the closing cut.
    ring=[(0,0),(0,1),(0,2),(1,2),(2,2),(2,1),(2,0),(1,0)]
    order=[]
    for start in range(8):
        seq=[]
        for h in range(8):
            p=ring[(start+h)%8];u,v=p;src=ring[(start+h-1)%8];dst=ring[(start+h+1)%8]
            # Traverse a corner in the outbound direction. Straight
            # rectangles have the same inbound and outbound direction.
            dr,dc=dst[0]-u,dst[1]-v
            cells=list(product(rows[u],cols[v]))
            cells.sort(key=lambda ij:(dr*ij[0]+dc*ij[1],ij[0]+ij[1]))
            seq+=cells
        order.append(seq)
    special=[((x+d,y),(x,y+e)) for x,d in ((lo,-1),(hi,1)) for y,e in ((le,-1),(ri,1))]
    special.append(((lo-1,le+1),(lo+1,le-1)))
    if two_gap:special.append(((lo-1,ri-1),(lo+1,ri+1)))
    if bridge:
        # Ordinary perimeter feet, in original board coordinates.
        p,r=bridge;special.append(((p[0]+a,p[1]+b),(r[0]+a,r[1]+b)))
    def input_for(seq):
        ix={p:i for i,p in enumerate(seq)};es=[[] for p in seq]
        for i,(x,y) in enumerate(seq):
            for pos in ((x-1,y),(x,y-1)):
                if pos in ix:
                    u,v=sorted((i,ix[pos]));es[v].append(u+1)
        for x,y in special:
            u,v=sorted((ix[x],ix[y]));es[v].append(-u-1)
        last=list(range(len(seq)))
        for i,ls in enumerate(es):
            for v in ls:last[abs(v)-1]=i
        diff=[0]*(len(seq)+1)
        for i,z in enumerate(last):diff[i]+=1;diff[z]-=1
        from itertools import accumulate
        return max(accumulate(diff)),es
    width,es,seq=min(((*input_for(seq),seq) for seq in order),key=lambda x:x[0])
    if pump:
        # Phase-aligned full slices in the homogeneous straight blocks.
        checks=[]
        for u,v in (ring[t] for t in (1,3,5,7)):
            loc=[i for i,(x,y) in enumerate(seq) if x in rows[u] and y in cols[v]]
            w=len(loc)//(n-2)
            checks.append((loc[12*w-1],loc[54*w-1]))
        return width,es,sorted(checks)
    return width,es

def solve(n,q,a,b):
    width,es=graph(n,q,a,b);txt=str(len(es))+'\n'+'\n'.join(' '.join(map(str,[len(z),*z])) for z in es)
    s=subprocess.run(['target/annular_frontier'],input=txt,text=True,capture_output=True,check=True)
    best,W,peak=map(int,s.stdout.split());assert width==W
    k=(n-2)//3;U=lambda k:3*k*k+7*k-(k-5)//7
    goal=4*n-9+U(k+q)-U(k)+1
    print(n,'growth',3*q,'shift',(a,b),'annulus max',best,'required',goal,'shortfall',goal-best,'width',W,'peak',peak,flush=True)
    return best
if __name__=='__main__':solve(*map(int,sys.argv[1:]))
