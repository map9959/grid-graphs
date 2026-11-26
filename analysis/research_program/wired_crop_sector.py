"""Deep square-sector upper on a crop with one external attachment per marked rim site."""
from collections import Counter
import sys
from .patch_square import relaxation
from .side28_score import solve
from .chart_counts import count

def model(base,d,w):
    def ok(i,j,kind,atom):
        if kind==0:
            f,nb,out=atom
            if '--leaf-sinks' in sys.argv and out==-1 and not (f and min(i,j,base-1-i,base-1-j)==0):
                if f or nb.count(1)>1:return False
            # Each marked boundary site is the sink of its component
            # after deleting the distinct attachments to the common root.
            return not f or min(i,j,base-1-i,base-1-j)>0 or out==-1
        for face,touches in (((0,1,2),i==0),((6,7,8),i==base-3),
                             ((0,3,6),j==0),((2,5,8),j==base-3)):
            if touches and sum((atom>>v)&1 for v in face)>1:return False
        return True
    ns,rows,obj=relaxation(base,d+4,pooled=d,period=3,diagonal=w,accept=ok)
    inv={v:k for k,v in ns.items()};A=[];keys=[]
    for cs,op,r in rows:
        if op=='>=':continue # no distinguished interior corner sink
        A.append((cs,op));keys.append(inv[cs[0][0]] if r else None)
    return ns,A,keys,obj

def inward(ns,base,d,w):
    from .patch_square import DIR,trans
    from .square_current import states
    cs=Counter();seen=set();h=d+4
    ax=lambda x:x if x<h else 2*h+3+x-base if x>=base-h else h+(x-h)%3
    cl=lambda z:max(-w-5,min(w+5,z))
    for i in range(base):
        for j in range(base):
            if min(i,j,base-1-i,base-1-j):continue
            pts=[(ax(u),ax(v),cl(u-v),cl(u+v+1-base)) for g in range(8) for u,v in [trans(i,j,base,g)]]
            if pts[0] in seen:continue
            seen.add(pts[0]);ds=[s for s,(a,b) in enumerate(DIR) if 0<=i+a<base and 0<=j+b<base]
            for f,sig in states(ds):
                out=next((s for s,v in sig.items() if v[2]==(1 if s<2 else -1)),-1)
                if f and out!=-1:continue
                nb=[sig[s][int(s<2)] if s in ds else 9 for s in range(4)]
                val=sum(bool(f or nb[s]) for s in ds if (s+2)%4 not in ds)
                if not val:continue
                opts=[]
                for g,p in enumerate(pts):
                    rot=lambda s:((2-s if g&4 else s)+g)%4;v=[9]*4
                    for s in ds:v[rot(s)]=nb[s]
                    opts.append((p,f,tuple(v),rot(out) if out>=0 else -1))
                cs[ns['s',min(opts)]]+=val
    return cs

def test(base,d,w,sizes):
    ns,A,keys,obj=model(base,d,w)
    cut='--near-sides' in sys.argv
    norm=Counter({x:2*v for x,v in obj.items()})
    if cut:
        norm.subtract(inward(ns,base,d,w));A.append((list(norm.items()),'<='))
    print('wired crop',len(ns),'atoms',len(A),'rows',flush=True)
    for n in sizes:
        assert (n-base)%6==0 and n>=base
        rhs=[count(n-2*(k[0]=='p'),d+4-(k[0]=='p'),w+5,k[1][0])[0] if k else 0 for k in keys]
        if cut:rhs.append(2*(n*n//3-n+5))
        v,_,_=solve(A,rhs,obj,ns,interior=True)
        print(n,'deficit',n*n/3-v,'target slope',7/30,flush=True)
if __name__=='__main__':
    import sys
    b,d,w,*n=map(int,[s for s in sys.argv[1:] if not s.startswith('--')]);test(b,d,w,n)
