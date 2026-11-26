"""Does the geometry-free side tariff improve the unrestricted sector relaxation?"""
from collections import Counter
from .patch_square import relaxation,trans,SYM,MASKS,DIR
from .square_current import states
from .chart_counts import count
from .side28_score import solve

def test(base,sizes):
    d=w=4
    ns,rows,obj=relaxation(base,8,pooled=4,period=3,diagonal=4)
    inv={x:k for k,x in ns.items()};A=[];rhs=[];keys=[]
    for row,op,v in rows:
        A.append((row,op));rhs.append(v);keys.append(inv[row[0][0]] if v and op=='=' else None)
    def pts(i,j,S):
        h=8-int(S!=base);ax=lambda x:x if x<h else 2*h+3+x-S if x>=S-h else h+(x-h)%3
        cl=lambda x:max(-9,min(9,x))
        return [(ax(u),ax(v),cl(u-v),cl(u+v+1-S)) for g in range(8) for u,v in [trans(i,j,S,g)]]
    marked=[Counter() for _ in range(7)]
    for i in range(7):
        seen=set()
        for j in range(base):
            z=pts(i,j,base)
            if z[0] in seen:continue
            seen.add(z[0]);ds=[s for s,(u,v) in enumerate(DIR) if 0<=i+u<base and 0<=j+v<base]
            for f,sig in states(ds):
                if not f:continue
                nb=[sig[s][int(s<2)] if s in ds else 9 for s in range(4)]
                out=next((s for s,e in sig.items() if e[2]==(1 if s<2 else -1)),-1);opts=[]
                for g,p in enumerate(z):
                    rot=lambda s:((2-s if g&4 else s)+g)%4;v=[9]*4
                    for s in ds:v[rot(s)]=nb[s]
                    opts.append((p,1,tuple(v),rot(out) if out>=0 else -1))
                marked[i][ns['s',min(opts)]]+=1
    bad={}
    for i in (0,3):
        S=base-2;cs=Counter();seen=set()
        for j in range(base):
            col=max(0,min(j-1,S-1));b=j-col;z=pts(i,col,S)
            if (z[0],b) in seen:continue
            seen.add((z[0],b))
            for m in MASKS:
                if (m>>b)&73!=1:cs[ns['p',min(zip(z,SYM[m]))]]+=1
        bad[i]=cs
    add=[]
    for h,aq,bq,C in ((3,10,20,70),(6,6,24,126)):
        total=sum(marked[:h],Counter())
        add.append((list(total.items()),'>=',h//3,0))
        for i in range(0,h,3):
            row=Counter({x:30*v for x,v in total.items()})
            for a,cs in ((aq,bad[i]),(bq,marked[h])):
                for x,v in cs.items():row[x]+=a*v
            add.append((list(row.items()),'<=',30*(h//3)+bq,C))
    for N in sizes:
        assert N>=base and (N-base)%6==0
        b=[count(N-2*(k[0]=='p'),8-(k[0]=='p'),9,k[1][0])[0] if k else v for k,v in zip(keys,rhs)]
        val,_,_=solve(A+[(r,op) for r,op,_,_ in add],b+[c*N+z for _,_,c,z in add],obj,ns,interior=True)
        k=N//3;old=3*k*k+16*k/3-7/6
        print('boundary-tariff LP side',N,'value',round(val,6),'old',round(old,6),'comb',3*k*k+5*k+(3*k-13)//10,flush=True)
if __name__=='__main__':test(55,[103,163])
