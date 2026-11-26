"""Test a (three west, three east, seven south) cover after an odd fan collision."""
from .north_fan_sync import Pool,cell,rowchart,fan,rectangle
from .synchronous_front import fold,prune

def attempt(c=15,L=8,s=18,rooted=16,guard=1):
    # Conditional experiment: the two outer fan runs have dangling
    # north components up to the rooted suffix. This driver does not
    # certify that partition for every enlarged north fan.
    a=32;r=a+1+rooted;W=a+r+c+6;P=Pool();H=s+L+9
    gaps=(12,a+3+c//2,W-rooted-13)
    rows=[fan(a+3*j,c-6*j,r+3*j) for j in range(2)]
    def raw(i,w):return cell(1,rowchart(i,w),7,-4)
    gd=[P.intern(raw(i,W) if j else raw(i,W)&{(rows[0][i],rows[1][i],rows[0][i+1],rows[1][i+1])})
        for j in range(H-1) for i in range(W-1)]
    def run(g,w,h,gs,rf,left,right,*,base=False):
        sealed=set(range(1,left-guard))|set(range(right+guard,rf-1))
        return prune(g,P,w,h,gs,rf,sealed=sealed)
    assert run(gd,W,H,gaps[::2],W-rooted,a-3,W-r+3)
    F=[[P.items[t] for t in gd[j*(W-1):(j+1)*(W-1)]] for j in range(s,s+L)]
    def edges(F):
        ms=[{p[0] for p in t} for t in F[0]]
        return next(x for x,t in enumerate(ms) if t!={448}),max(x+1 for x,t in enumerate(ms) if t!={7})
    e=edges(F);w=W+6;h=L+16
    for n in range(16):
        gd=[]
        for j in range(h-1):
            for i in range(w-1):
                k=fold(fold(i,gaps[2]+3),gaps[0])
                d=cell(2,rowchart(i,w),7,-4)
                gd.append(P.intern(d if j>=L else d&F[j][k]))
        assert run(gd,w,h,(gaps[0],gaps[1]+3,gaps[2]+3),w-rooted,e[0]+3,e[1]+3)
        new=[a.copy() for a in F]
        for j in range(L):
            for i in range(w-1):
                x=fold(i,gaps[1],6)
                new[j][x]=new[j][x]|P.items[gd[(7+j)*(w-1)+i]]
        print(n,edges(new),sum(x!=y for a,b in zip(F,new) for x,y in zip(a,b)),flush=True)
        if F==new:return True
        if edges(new)!=e:return False
        F=new
    return False
if __name__=='__main__':
    import sys
    print(attempt(*map(int,sys.argv[1:])))
