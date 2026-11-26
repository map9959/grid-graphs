"""Search the remaining individual charge-72 locations, without orbit averaging."""
from .odd_charge_parity import build,possible
import sys
from collections import Counter

def run():
    import highspy as H
    import numpy as np
    n=35;cols,qs,_,nr,labels,rd,mass=build(n)
    take=possible(cols,qs,rd,mass,labels,(72,))
    if '--dimers' in sys.argv:
        from .charge_dimers import extend
        extend(n,cols,qs,rd,mass,labels,take)
        for i,t in enumerate(take):
            if not t:qs[i]=73
        take=possible(cols,qs,rd,mass,labels,(72,))
    nr=len(rd);incident=[[] for _ in range(nr)];vars=[];rare=[]
    for i,(ok,col,q) in enumerate(zip(take,cols,qs)):
        if not ok:continue
        j=len(vars);vars.append(i)
        for r in col:incident[r if r>=0 else ~r].append((j,1 if r>=0 else -1))
        if q:rare.append(j)
    N=len(vars);rhs=Counter()
    depth=int(next((s[2:] for s in sys.argv if s.startswith('d=')),6))
    for (t,r,c),m in mass.items():
        row=rd['norm',(t,r,c)];d=depth-t;S=n-2*t
        def count(z):
            return ((S-2*d+5-(z-d))//6,7) if d<=z<d+6 else (1,0)
        a,u=count(r);b,v=count(c);assert a*b==m
        inc=a*v+b*u+u*v;dd=2*u*v
        rhs[row]=m
        if inc:incident[row].append((N,-inc))
        if dd:incident[row].append((N+1,-dd))
    row=rd['score',];incident[row].extend([(N,-1608),(N+1,-1176)]);rhs[row]=440
    incident.append([(j,1) for j in rare]);rhs[nr]=1
    h=H.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
    h.setOptionValue('solver','simplex')
    h.addVars(N+2,np.zeros(N+2),np.full(N+2,H.kHighsInf))
    for i,row in enumerate(incident):
        cs=Counter()
        for j,w in row:cs[j]+=w
        if cs:h.addRow(rhs[i],rhs[i],len(cs),list(cs),list(cs.values()))
    print('uniform matching test',len(incident),N,'candidate atoms',len(rare),flush=True)
    good=[]
    def solve(js,depth):
        h.run();st=h.getModelStatus()
        if st==H.HighsModelStatus.kUnknown:
            h.clearSolver();h.setOptionValue('solver','ipm');h.run();st=h.getModelStatus();h.setOptionValue('solver','simplex')
        if st==H.HighsModelStatus.kInfeasible:return
        assert st==H.HighsModelStatus.kOptimal,st
        if len(js)==1:good.append(labels[vars[js[0]]]);return
        if depth<=2:print('branch',depth,len(js),flush=True)
        halves=[js[:len(js)//2],js[len(js)//2:]]
        for keep,omit in (halves,halves[::-1]):
            h.changeColsBounds(len(omit),np.array(omit),np.zeros(len(omit)),np.zeros(len(omit)))
            solve(keep,depth+1)
            h.changeColsBounds(len(omit),np.array(omit),np.zeros(len(omit)),np.ones(len(omit)))
    solve(rare,0)
    print('numerically surviving singleton events',len(good),good,flush=True)
if __name__=='__main__':run()
