"""Complementary face ownership for tile marks after attaching the unique isolate."""
from itertools import product,combinations
from .odd_frames import frame
from .defect_window import DIR

def install(f,vp,n,domains,tile,flags,d0,tree):
    mark=lambda i,j:vp.id(('mark',i,j))
    for (i,j),ms in domains.items():
        for m in ms:
            z=tile(i,j,m)
            for a,b in product(range(3),repeat=2):
                p=mark(1+3*i+a,1+3*j+b);f.append([-z,p if m>>(3*a+b)&1 else -p])
    for u,b in frame(n,(0,1,3,3)).items():f.append([mark(*u)*(1 if b else -1)])
    if not flags:
        s=vp.id();f.append([s]);flags={d0:s}
    for d,s in flags.items():
        for a,b in ((0,0),*DIR):f.append([-s,-mark(2+a,d+b)])
    owner=lambda i,j,k:vp.id(('face',i,j,k))
    face=lambda i,j:0<=i<n-1 and 0<=j<n-1
    for i,j in product(range(n),repeat=2):
        if face(i,j):
            vs=[owner(i,j,k) for k in range(4)];f.append(vs)
            for x,y in combinations(vs,2):f.append([-x,-y])
            if tree:
                for k,(a,b) in enumerate(DIR):
                    if not face(i+a,j+b):continue
                    x=vp.id(('fsheet',i,j));y=vp.id(('fsheet',i+a,j+b))
                    for h in range(4):
                        if h==(k+2)%4:continue
                        z=y*(-1 if abs(h-k)==3 else 1);g=[-vs[k],-owner(i+a,j+b,h)]
                        f.extend([g+[-x,z],g+[x,-z]])
        for h,(di,dj) in enumerate(DIR[:2]):
            v=i+di,j+dj
            if max(v)>=n:continue
            tags=((i,j,3),(i-1,j,1)) if h==0 else ((i,j,2),(i,j-1,0))
            fs=[owner(r,c,k) for r,c,k in tags if face(r,c)]
            ext=flags.get(j) if h==1 and i==1 else None
            for z in fs:
                f.extend([[-z,-mark(i,j)],[-z,-mark(*v)]])
                if ext:f.append([-z,-ext])
            if len(fs)==2:f.append([-fs[0],-fs[1]])
            f.append(fs+[mark(i,j),mark(*v)]+([ext] if ext else []))
