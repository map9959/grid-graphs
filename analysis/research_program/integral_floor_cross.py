"""An integral cross with a common raw component partition and physical tree refill."""
from itertools import combinations,product
from .physical_mark_count import add as atleast
from .skeleton_cross_rank import DSU


def add_cross(model,y,x,required_loss=None):
    n=model.n;s=n-1;p=model.p;f=model.f
    def site(i,j):return model.X[i+(i>=y)][j+(j>=x)]
    D=((0,1),(1,0),(0,-1),(-1,0))
    O={};labels={};sheet={};E={};forced={}
    for i,j in product(range(s),repeat=2):
        dirs={t:p.id() for t,(a,b) in enumerate(D) if 0<=i+a<s and 0<=j+b<s}
        O[i,j]=dirs;sheet[i,j]=p.id()
        labels[i,j]=[p.id() for _ in range((s*s-1).bit_length())]
        if i or j:f.append(list(dirs.values()))
        else:
            for z in dirs.values():f.append([-z])
        for a,b in combinations(dirs.values(),2):f.append([-a,-b])
    for i,j in product(range(s),repeat=2):
        for t,z in O[i,j].items():
            di,dj=D[t];u,v=i+di,j+dj
            if t<2:
                rev=O[u,v][t+2];f.append([-z,-rev])
                e=model.disj([z,rev]);E[i,j,t]=E[u,v,t+2]=e
                l,r=site(i,j),site(u,v)
                a=model.disj([l,r]);forced[i,j,t]=forced[u,v,t+2]=a
                # Outside a seam all raw compulsory bonds remain.
                # Across either seam preserve each supported subdivision.
                if not (di and u==y or dj and v==x):f.append([-a,e])
                else:
                    middle=(model.X[y][j+(j>=x)] if di else model.X[i+(i>=y)][x])
                    f.extend([[-l,-r,e],[-a,-middle,e]])
                # Every raw bond, including a rejected one, joins equal labels.
                for l,r in zip(labels[i,j],labels[u,v]):
                    f.extend([[-a,-l,r],[-a,l,-r]])
            for t2,z2 in O[u,v].items():
                if t2==(t+2)%4:continue
                b=sheet[u,v]*(-1 if abs(t-t2)==3 else 1)
                f.extend([[-z,-z2,-sheet[i,j],b],[-z,-z2,sheet[i,j],-b]])
    full={};paid=[];gain=[]
    for i,j in product(range(s),repeat=2):
        # Restrict the oriented spanning tree to its raw bonds. At
        # each resulting sink the common label equals its own ID:
        # this forces the kept raw forest to span every raw component.
        par=[model.conj([o,forced[i,j,t]]) for t,o in O[i,j].items()]
        for h,b in enumerate(labels[i,j]):f.append([*par,b if (i*s+j)>>h&1 else -b])
        full[i,j]=model.conj([E[i,j,t] for t in O[i,j]])
        a=site(i,j)
        if i in (y-1,y) or j in (x-1,x):
            paid.append(model.conj([a,-full[i,j]]))
        gain.append(model.conj([-a,full[i,j]]))
    if required_loss is not None:
        assert required_loss>0
        erased=[model.X[i][j] for i,j in product(range(n),repeat=2) if i==y or j==x]
        losses=erased+paid
        if len(losses)<required_loss:f.append([])
        else:atleast(f,p,losses+[-z for z in gain],required_loss+len(gain))
    return full,E,forced


def replay_cross(model,board,val):
    n=model.n;s=n-1;y,x,full,edges,forced=model.cross
    true=lambda z:(abs(z) in val)==(z>0)
    kept=DSU(s*s);raw=DSU(s*s);tree=DSU(s*s);lost=cycles=nt=0
    for (i,j,t),a in edges.items():
        if t>=2:continue
        u=i*s+j;v=u+(1 if t==0 else s);on=true(forced[i,j,t]);use=true(a)
        if on:
            cycles+=not raw.join(u,v)
            if use:assert kept.join(u,v)
            else:lost+=1
        if use:assert tree.join(u,v);nt+=1
    assert nt==s*s-1 and lost==cycles
    # Independent reconstruction of actual full degrees.
    for (i,j),z in full.items():
        assert true(z)==all(true(edges[i,j,t]) for t in range(4) if (i,j,t) in edges)
    size=sum(true(z) for z in full.values())
    print('paired cross',(y,x),'cycle rank',cycles,'physical tree',nt,'full',size,
          'net loss',sum(r.count('#') for r in board)-size,flush=True)
