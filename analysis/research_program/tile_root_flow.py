"""Orient every forced crop edge toward the unique tooth of its component."""
from itertools import product,combinations
from .defect_window import DIR

def install(f,vp,n,domains,tile,flags,d0):
    def mark(i,j):return vp.id(('mark',i,j))
    for (i,j),ms in domains.items():
        for m in ms:
            for a,b in product(range(3),repeat=2):
                z=mark(1+3*i+a,1+3*j+b);f.append([-tile(i,j,m),z if m>>(3*a+b)&1 else -z])
    if not flags:
        z=vp.id();f.append([z]);flags={d0:z}
    for i,j in product(range(2,n-2),repeat=2):
        outs=[]
        for d,(a,b) in enumerate(DIR):
            x,y=i+a,j+b
            if not(2<=x<n-2 and 2<=y<n-2):continue
            v=vp.id(('crop_arrow',i,j,d));outs.append(v)
            if d>=2:continue
            w=vp.id(('crop_arrow',x,y,d+2));s,t=mark(i,j),mark(x,y)
            f.extend([[-v,-w],[-s,v,w],[-t,v,w],[-v,s,t],[-w,s,t]])
        for v,w in combinations(outs,2):f.append([-v,-w])
        exceptions=[]
        if min(i,j,n-1-i,n-1-j)==2:exceptions.append(mark(i,j))
        if i==2 and j in flags:exceptions.append(flags[j])
        f.append(outs+exceptions)
        for z in exceptions:
            for v in outs:f.append([-z,-v])
