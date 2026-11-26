"""Free outer boundary transfer coupled to a rooted rail cap of unbounded height."""
from collections import Counter
from functools import lru_cache
from .seam_rank_chart import model
from .sector_oriented import move,masks,assign
import sys

def run(H,N,d,B):
    import highspy as hs
    import numpy as np
    assert '--free-top' in sys.argv and H>=2*(d+4)+3 and B-1<=d+4
    A,b,obj,ns,norms=model(H,N,d);ix={x:i for i,x in enumerate(ns.values())}
    h=hs.Highs();h.setOptionValue('output_flag',False);h.setOptionValue('threads',1)
    h.setOptionValue('solver','ipm');h.setOptionValue('run_crossover','off')
    I=hs.kHighsInf;h.addVars(len(ix),np.zeros(len(ix)),np.full(len(ix),I))
    h.changeColsCost(len(ix),np.arange(len(ix)),[float(obj.get(x,0)) for x in ix]);h.setMaximize()
    def row(rhs,cs=()):
        z=h.getNumRow();h.addRow(rhs,rhs,len(cs),[x for x,_ in cs],[v for _,v in cs]);return z
    for (ls,op),z in zip(A,b):row(z,[(ix[x],v) for x,v in ls])
    def ax(j,S,depth):return j if j<depth else 2*depth+3+j-S if j>=S-depth else depth+(j-depth)%3
    depth=d+6;ph=lambda j:ax(j,N,depth)
    @lru_cache(None)
    def bind(name):return row(0,[(ix[ns[name]],-1)])
    @lru_cache(None)
    def flow(j,s):return row(0)
    @lru_cache(None)
    def trans(s,final):
        a,b,P,west=s;ans=[]
        for c in ([0] if final else range(1<<B)):
            part=P if final else move(b,P,c)
            if part is None:continue
            for right,ds in assign(b,west,0 if final else b|c,B):
                ans.append(((b,c,part,right),masks(a,b,c,B),ds))
        return ans
    one=row(1);st=set()
    for b0 in range(1<<B):
        s=(0,b0,move(0,tuple(range(B)),b0),0);st.add(s);h.addCol(0,0,I,2,[one,flow(ph(0),s)],[1,-1])
    keys=[(ph(j),ph(j+1) if j+1<N else -1) for j in range(N)]
    count=Counter(keys);seen=set();stage=[]
    for j,(cur,nxt) in enumerate(keys):
        if (cur,nxt) in seen:continue
        if j==depth:
            while True:
                new={u for s in st for u,_,_ in trans(s,False)}
                if new<=st:break
                st|=new
        seen.add((cur,nxt));nr=row(count[cur,nxt]);stage.append((nr,cur,nxt))
        dst=set();starts=[];col=[];val=[]
        for s in sorted(st):
            a,b0,_,_=s
            for u,ms,ds in trans(s,nxt<0):
                c=u[1];ids=[flow(cur,s),nr];v=[1,1]
                if nxt>=0:ids.append(flow(nxt,u));v.append(-1);dst.add(u)
                if 0<j<N-1:
                    for r,m in enumerate(ms):ids.append(bind(('p',(r,ax(j-1,N-2,d+3)),m)));v.append(1)
                for r in range(B-1):
                    nb=(c>>r&1 if nxt>=0 else 9,b0>>(r+1)&1,a>>r&1 if j else 9,b0>>(r-1)&1 if r else 9)
                    ids.append(bind(('s',(r,ax(j,N,d+4)),b0>>r&1,nb,ds[r])));v.append(1)
                starts.append(len(col));col.extend(ids);val.extend(v)
        h.addCols(len(starts),np.zeros(len(starts)),np.zeros(len(starts)),np.full(len(starts),I),len(col),starts,col,val)
        st=dst
    print('seam surface depth',B,'columns',h.getNumCol(),'rows',h.getNumRow(),flush=True)
    h.run();assert h.getModelStatus()==hs.HighsModelStatus.kOptimal
    dual=h.getSolution().row_dual;val=h.getObjectiveValue();slope=0
    for i,k in enumerate(norms):
        if k:
            t,(r,c)=k;f=d+4-t
            if f<=c<f+3:slope+=dual[i]*(1+(H-2*t-1-f-r)//3 if f<=r<f+3 else 1)
    slope+=sum(dual[i] for i,a,b in stage if depth<=a<depth+3 and depth<=b<depth+3)
    print('weighted upper',val,'excess',val-H*(N//3+1),'width +3 surface increment',slope-H,flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:5]))
