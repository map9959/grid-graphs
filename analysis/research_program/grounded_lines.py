"""No two perpendicular straight attachments on one forced row/column segment."""
from itertools import combinations

def install(n,top,bit,add):
    # Each true flag is mandatory when the corresponding line is forced:
    # the implications suffice, with the converse used to aid propagation.
    def new():
        nonlocal top
        top+=1;return top
    def propagate(q,a,b,z):
        # z iff q and (a or b), or just (a or b) at a boundary foot.
        pre=[] if q is None else [-q]
        add(*pre,-a,z);add(*pre,-b,z)
        if q is not None:add(-z,q)
        add(-z,a,b)
    ids={}
    for axis in (0,1):
        for line in range(1,n-1):
            pos=lambda k:(line,k) if axis==0 else (k,line)
            for step in (1,-1):
                q=None
                for k in (range(1,n-1) if step==1 else range(n-2,0,-1)):
                    u=pos(k);z=new()
                    propagate(q,bit(*pos(k-step)),bit(*u),z)
                    ids[u,axis,step]=z;q=z
    for axis in (0,1):
        for line in range(1,n-1):
            pos=lambda k:(line,k) if axis==0 else (k,line)
            q=None
            for k in range(1,n-1):
                u=pos(k);z=new()
                propagate(q,bit(*pos(k-1)),bit(*u),z)
                a,b=(ids[u,1-axis,step] for step in (1,-1))
                # Distinct perpendicular feet, plus the earlier attachment
                # (a different column/row or the start of the line).
                for x,y in combinations((z,a,b),2):add(-x,-y)
                q=new()
                for x in (z,a,b):add(-x,q)
                add(-q,z,a,b)
            for x in (bit(*pos(n-2)),bit(*pos(n-1))):add(-q,-x)
    return top
