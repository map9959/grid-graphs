"""Two-tile strip transfers including face potentials modulo two."""
from itertools import product
from .tile_circulation import enumerate_blocks
import sys

def graph(blocks,phase,axis):
    G=set()
    for w in blocks:
        if any(m&16 and m&(40 if axis==1 else 130) for m in w):continue
        mark=lambda i,j:w[2*(i//3)+j//3]>>(3*(i%3)+j%3)&1
        adj=[[] for _ in range(25)]
        for i,j in product(range(5),repeat=2):
            u=5*i+j
            if j<4 and not(mark(i,j+1) or mark(i+1,j+1)):adj[u].append((u+1,0));adj[u+1].append((u,0))
            if i<4 and not(mark(i+1,j) or mark(i+1,j+1)):
                z=(phase+j)%2;adj[u].append((u+5,z));adj[u+5].append((u,z))
        ids={};ofs={};k=0;ok=True
        for s in range(25):
            if s in ids:continue
            ids[s]=k;ofs[s]=0;q=[s]
            for u in q:
                for v,z in adj[u]:
                    if v not in ids:ids[v]=k;ofs[v]=ofs[u]^z;q.append(v)
                    elif ofs[v]!=ofs[u]^z:ok=False
            k+=1
        if not ok:continue
        # Only components meeting at least one end matter.
        ends=[[5*i+j+shift for i,j in product(range(5),range(2))] for shift in (0,3)]
        reps={v:i for i,v in enumerate(sorted({ids[u] for us in ends for u in us}))}
        for c in range(1<<len(reps)):
            pair=[]
            for side,us in enumerate(ends):
                pot=sum(((c>>reps[ids[u]]&1)^ofs[u])<<i for i,u in enumerate(us))
                pair.append((w[side],w[side+2],pot))
            G.add(tuple(pair))
    return G

def run(axis,phase=0):
    assert phase in (0,1)
    B=enumerate_blocks(0);gs=[graph(B,p,axis) for p in (0,1)]
    nodes=sorted({u for g in gs for p in g for u in p});ix={u:i for i,u in enumerate(nodes)}
    print('states',len(nodes),'edges per parity',list(map(len,gs)),flush=True)
    # Simultaneous complementation of the 10 end bits is a symmetry.
    reps={v:i for i,v in enumerate(n for n in nodes if not n[2]&1)}
    # Process entrance orbits in batches to bound memory for all powers.
    ans=0
    for start in range(0,len(reps),512):
        adj=[[(ix[u],ix[v]) for u,v in g] for g in gs]
        old=[1<<(reps[u]-start) if start<=reps.get(u,-1)<start+512 else 0 for u in nodes]
        hist=[old]
        for t in range(1,70):
            new=[0]*len(nodes)
            for u,v in adj[(phase+t-1)%2]:new[v]|=old[u]
            if t>=14 and new==hist[(t-14)%14]:ans=max(ans,t-14);break
            if len(hist)<14:hist.append(new)
            else:hist[t%14]=new
            old=new
        else:raise AssertionError('no 14-step stabilization yet')
    print('axis',axis,'dual-area transfer: length l equivalent to l+14 for all l >=',ans,'at starting parity',phase)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
