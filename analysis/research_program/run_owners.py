"""One claimed join per run (apart from the rooted run); one run per join."""
from itertools import product,combinations
from .square_dual_physical import DIR

def install(n,top,bit,add,path):
    def owner(i,j,d):return top+6*(i*n+j)+d+1
    def dep(i,j):return min(i,j,n-1-i,n-1-j)
    for i,j in product(range(n),repeat=2):
        v=bit(i,j);claim=owner(i,j,4);seen=owner(i,j,5)
        at=[(i+a,j+b) for a,b in DIR];choices=[]
        for d,(x,y) in enumerate(at):
            a,b=DIR[d];h,k=x+a,y+b
            if dep(h,k)<0:continue
            z=owner(i,j,d);choices.append(z)
            add(-z,v);add(-z,-bit(x,y));add(-z,bit(h,k))
            if d<2:
                w=owner(h,k,d+2);add(-z,-w);add(-v,bit(x,y),-bit(h,k),z,w)
            if (x,y) in path and path[x,y]!=(d+2)%4:
                # If midpoint points to the far end, source owns the join.
                if path[x,y]==d:add(-v,bit(x,y),-bit(h,k),z)
        for a,b in combinations(choices,2):add(-a,-b)
        if (i,j)==(0,0):
            add(claim)
            for z in choices:add(-z)
        else:
            for z in choices:add(-z,claim)
            add(-claim,*choices)
        # Prefix of the maximal straight marked run: north/west predecessor
        # is unique by diagonal exclusion. seen records one exit so far.
        add(-seen,v);add(-claim,seen)
        prev=[]
        for d in (2,3):
            x,y=at[d]
            if dep(x,y)<0:continue
            p=bit(x,y);g=owner(x,y,5);prev.append(p)
            add(-v,-g,seen);add(-v,-g,-claim);add(-seen,-p,g,claim)
        add(-seen,claim,*prev)
        add(-v,seen,*(bit(*at[d]) for d in (0,1) if dep(*at[d])>=0))
        if dep(i,j)==2:
            for d,(a,b) in enumerate(DIR):
                x,y=i+2*a,j+2*b
                if dep(x,y)==0:add(-v,-bit(x,y),owner(i,j,d))
    return top+6*n*n
