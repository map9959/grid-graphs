"""Fill all isolated straight-rim holes at once; deeper marks need not be aligned."""
from .sparse_component_exchange import graph
from .extend_forest_28 import verify
from .wired_crop_exchange import ring

def fill(rows):
    n=len(rows);assert n>=6
    f=list(map(list,rows));M={(i,j) for i,r in enumerate(rows) for j,c in enumerate(r) if c=='#'}
    jobs=[];clip=set()
    for side in range(4):
        def at(y,x):
            for _ in range(side):y,x=x,n-1-y
            return y,x
        for x in range(2,n-2):
            p=at(0,x)
            if p in M or not {at(0,x-1),at(0,x+1)}<=M:continue
            q,w=at(1,x),at(2,x)
            adj=M&{at(1,x-1),at(1,x+1)}
            assert len(adj)<=1 and q not in M and not(adj and w in M)
            clip|=adj;jobs.append((p,q,w))
    for y,x in clip:f[y][x]='.'
    F=graph(f,set());drop=set();rho=0
    for p,q,w in jobs:
        if F.join(p,q):rho+=1
        else:assert w in M;drop.add(w)
    assert rho>=len(clip)
    for y,x in drop:f[y][x]='.'
    for (y,x),_,_ in jobs:f[y][x]='#'
    out=[''.join(s) for s in f];tree=verify(out)
    gain=tree[0]-len(M);assert gain>=rho-len(clip)
    w=[out[y][x] for y,x in ring(n)]
    g=sum(a==b=='.' for a,b in zip(w,w[1:]+w[:1]))
    assert w.count('.')<=2*g+8
    return out,(len(jobs),len(clip),rho,len(drop),gain,g,w.count('.'),tree)

if __name__=='__main__':
    from .comb_cap_transfer import construct
    from .dense_joint_collar import punctures
    r=list(map(list,construct(103,4)))
    for j in range(10,90,7):r[0][j]='.'
    print('punctured comb',fill(r)[1])
    # A single inward clip frees two spokes. Include a separate block
    # of adjacent vacancies; neither of its sites is a target.
    r=[['.']*22 for _ in range(22)];r[0]=list('####.##.#.#####..#####')
    r[1][8]='#';print('shared inward clip',fill(r)[1])
    print('cropped returns',fill([s[9:-9] for s in punctures(103,True)[9:-9]])[1])
