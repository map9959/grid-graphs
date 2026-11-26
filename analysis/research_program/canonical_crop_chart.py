"""Sector test on the canonical exterior of an arbitrary wired crop."""
from .patch_square import DIR,trans,relaxation
from .wired_crop_sector import solve,count
from .wired_crop_exchange import ring

def test(base,d,w,nsizes):
    frame=set(ring(base))-{(0,1),(0,2),(1,base-1),(base-1,base-2),(base-2,0)}
    def plain(i,j):
        dp=min(i,j,base-1-i,base-1-j)
        if dp<2:return int((i,j) in frame)
        if i in (2,base-3) and j in (2,base-3):return 0
    def allowed(i,j,kind,atom):
        if kind==1:
            return all(v is None or v==atom>>(3*a+b)&1
                       for a in range(3) for b in range(3) for v in [plain(i+a,j+b)])
        f,nb,out=atom
        if plain(i,j) not in (None,f):return False
        for s,(a,b) in enumerate(DIR):
            u,v=i+a,j+b
            if 0<=u<base and 0<=v<base and plain(u,v) not in (None,nb[s]):return False
        if f and min(i,j,base-1-i,base-1-j)==2:
            # The chosen frame may omit its foot. Orient even the
            # disconnected tree towards this tooth and its outer leaf.
            return out in [s for s,(a,b) in enumerate(DIR)
                           if min(i+a,j+b,base-1-i-a,base-1-j-b)==1]
        return True
    # Asymmetric canonical rim: no D4 identifications. Root at its NW
    # corner; the NW star must be a sink. Other components root freely.
    ns,rows,obj=relaxation(base,d+4,pooled=d,period=3,diagonal=w,rooted=True,group_override=(0,),accept=allowed)
    inv={v:k for k,v in ns.items()};A=[];keys=[]
    for cs,op,r in rows:
        A.append((cs,op));keys.append(inv[cs[0][0]] if r else None)
    print('canonical',len(ns),len(A),flush=True)
    for n in nsizes:
        rhs=[count(n-2*(k[0]=='p'),d+4-(k[0]=='p'),w+5,k[1][0])[0] if k else 0 for k in keys]
        v,_,_=solve(A,rhs,obj,ns,interior=True)
        k=n//3;print(n,'canonical real excess over quadratic + 5k',v-3*k*k-5*k,flush=True)
if __name__=='__main__':
    import sys
    b,d,w,*n=map(int,sys.argv[1:]);test(b,d,w,n)
