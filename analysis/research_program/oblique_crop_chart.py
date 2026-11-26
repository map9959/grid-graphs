"""Price oblique lines along which exposed pitch runs can exchange ends."""
from .patch_square import relaxation
from .wired_crop_sector import solve
import sys

def test(n,slope,d,w):
    wired='--free' not in sys.argv
    def accept(i,j,kind,atom):
        if not wired:return True
        if kind==0:
            f,nb,out=atom
            return not f or min(i,j,n-1-i,n-1-j)>0 or out==-1
        for face,on in (((0,1,2),i==0),((6,7,8),i==n-3),
                        ((0,3,6),j==0),((2,5,8),j==n-3)):
            if on and sum((atom>>v)&1 for v in face)>1:return False
        return True
    def rays(i,j,S,fine):
        # Distance to the nearer side on each axis is 1-Lipschitz;
        # an offset by 2 in a patch can change either distance by at most 2.
        x=min(i,S-1-i);y=min(j,S-1-j);clip=1+(2*slope+3 if fine else 0)
        return tuple(max(-clip,min(clip,z)) for z in (x-y*slope,y-x*slope))+tuple(
            max(-6,min(6,z)) for z in (2*i+1-S,2*j+1-S)) if fine else tuple(
            max(-clip,min(clip,z)) for z in (x-y*slope,y-x*slope))
    ns,rows,obj=relaxation(n,d+4,pooled=d,period=3,diagonal=w,accept=accept,rays=rays)
    A=[];b=[]
    for cs,op,v in rows:
        if wired and op=='>=':continue
        A.append((cs,op));b.append(v)
    score,_,_=solve(A,b,obj,ns,interior=True);print(n,len(ns),len(A),'score',score,'offset from bulk',score-n*n/3,flush=True)
if __name__=='__main__':
    slope,d,w,*ns=map(int,[s for s in sys.argv[1:] if not s.startswith('--')])
    for n in ns:test(n,slope,d,w)
