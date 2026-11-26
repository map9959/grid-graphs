"""Lexicographic local dominance for arbitrary exterior wiring at an actual rim."""
from functools import lru_cache
from itertools import product

@lru_cache(None)
def cubes(h,w,corner=False,ordered=False,words=False):
    N=h*w;assert N<=18
    ports=[j for j in range(N) if j//w==h-1 or j%w==w-1 or not corner and j%w==0]
    rim=sum(1<<j for j in range(N) if j<w or corner and j%w==0)
    cut=sum(1<<j for j in ports);edges=[(i,j,(1<<i)|(1<<j)) for i in range(N)
        for j in (i+1,i+w) if j<N and (j!=i+1 or j%w!=0)]
    groups={};allwords=[]
    for m in range(1<<N):
        p=list(range(N))
        def rt(v):
            while p[v]!=v:v=p[v]
            return v
        for u,v,bits in edges:
            if not bits&m:continue
            a,b=rt(u),rt(v)
            if a==b:break
            p[a]=b
        else:
            roots=list(map(rt,ports));part=sum(1<<(i*len(ports)+j) for i,x in enumerate(roots) for j in range(i) if roots[j]==x)
            key=m&cut;score=m.bit_count(),(m&rim).bit_count()
            if ordered:
                assert corner
                score+=(m&1,(m>>1)&1)
            g=groups.setdefault(key,{});g[part]=max(g.get(part,(-1,-1)),score)
            allwords.append((m,key,part,score))
    bad=[];survive=[]
    for m,key,p,s in allwords:
        if any(z>s and a&~p==0 for a,z in groups[key].items()):bad.append(m)
        else:survive.append(m)
    if words:return tuple(survive)
    # A cube can also exclude an internally cyclic word, but must avoid
    # every feasible nondominated word. Greedily minimize the premises.
    lit=[[sum(1<<i for i,m in enumerate(survive) if (m>>j)&1==b)
          for b in (0,1)] for j in range(N)]
    full=(1<<len(survive))-1;cover=[]
    for m in bad:
        if any(m&keep==value for keep,value in cover):continue
        left=full;cols=[]
        while left:
            j=min(range(N),key=lambda a:(lit[a][m>>a&1]&left).bit_count())
            cols.append(j);left&=lit[j][m>>j&1]
        for j in cols[:]:
            t=full
            for a in cols:
                if a!=j:t&=lit[a][m>>a&1]
            if not t:cols.remove(j)
        keep=sum(1<<j for j in cols);cover.append((keep,m&keep))
    assert all(not any(m&k==v for k,v in cover) for m in survive)
    if ordered:
        print('surviving corner, favored port, other port:',sorted({(m&1,m>>1&1,m>>w&1) for m in survive}))
        if (h,w)==(4,4):
            assert all(m&1 and ((m>>1^m>>w)&1) for m in survive)
            assert all(m&2 or not m&4 for m in survive)
    print('corner' if corner else 'side',h,w,'dominated',len(bad),'survivors',len(survive),'cubes',len(cover),flush=True)
    return cover

def forbid(f,X,n,D,h,w,rot=None):
    from .patch_square import trans
    for side in (range(4) if rot is None else [rot]):
        for left in range(1,n-w):
            pts=[trans(y,x+left,n,side) for y,x in product(range(h),range(w))]
            if not all(v in D for v in pts):continue
            ids=[X[i*n+j] for i,j in pts]
            for k,v in cubes(h,w):
                f.append([-x if v>>j&1 else x for j,x in enumerate(ids) if k>>j&1])
        for flip in (0,1):
            pts=[trans(x if flip else y,y if flip else x,n,side) for y,x in product(range(h),range(w))]
            if all(v in D for v in pts):
                ids=[X[i*n+j] for i,j in pts]
                for k,v in cubes(h,w,True):f.append([-x if v>>j&1 else x for j,x in enumerate(ids) if k>>j&1])

if __name__=='__main__':
    for h,w in ((3,4),(3,5),(4,4)):
        cubes(h,w);cubes(h,w,True)
