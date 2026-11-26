"""Test whole-square diagonal mass transport under the necessary one-gap frame."""
from .odd_charge_parity import build,possible,Counter,DIR,product
from .odd_frames import frame
import sys

def run(n,sector,word):
    import highspy as H
    import numpy as np
    cols,qs,_,_,labs,rd,mass=build(n,sector=sector);marks=frame(n,word)
    p={(0,0):-1};todo=[(0,0)]
    for i,j in todo:
        for d,(a,b) in enumerate(DIR):
            z=i+a,j+b
            if z in marks and min(*z,n-1-z[0],n-1-z[1])==0 and z not in p and (marks[i,j] or marks[z]):
                p[z]=(d+2)%4;todo.append(z)
    known={}
    for t in range(2):
        S=n-2*t;h=6-t
        ax=lambda j:j if j<h else 2*h+6+j-S if j>=S-h else h+(j-h)%6
        for i,j in product(range(S),repeat=2):
            k=(t,ax(i),ax(j))+(tuple(max(-sector,min(sector,z)) for z in (i-j,i+j+1-S)) if sector else ())
            v=tuple(marks.get((i+a,j+b)) for a,b in product(range(3),repeat=2)) if t else (marks.get((i,j)),*(marks.get((i+a,j+b)) for a,b in DIR),p.get((i,j)))
            assert known.setdefault(k,v)==v
    for i,(k,v) in enumerate(labs):
        if qs[i] not in (0,72):continue
        vv=tuple((v>>j)&1 for j in range(9)) if k[0] else (v[0],*v[1],v[2])
        if any(a is not None and a!=b for a,b in zip(known[k],vv)):qs[i]=73
    take=possible(cols,qs,rd,mass,labs,(72,))
    if not take:print('support vanishes',flush=True);return
    use=[i for i,t in enumerate(take) if t];rare=[]
    incidence=[[] for _ in range(len(rd))]
    for j,i in enumerate(use):
        if qs[i]:rare.append(j)
        for r in cols[i]:incidence[r if r>=0 else ~r].append((j,1 if r>=0 else -1))
    rhs=Counter({rd['norm',k]:v for k,v in mass.items()});k=(n-2)//3;rhs[rd['score',]]=3*k*k+7*k-(k-5)//7
    incidence.append([(j,1) for j in rare]);rhs[len(rd)]=1
    h=H.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False);h.setOptionValue('solver','ipm');h.setOptionValue('run_crossover','off')
    h.addVars(len(use),np.zeros(len(use)),np.full(len(use),H.kHighsInf));seen=set()
    for i,terms in enumerate(incidence):
        v=Counter()
        for j,a in terms:v[j]+=a
        row=tuple((j,w) for j,w in v.items() if w)
        if not row and not rhs[i]:continue
        if row and row[0][1]<0:row=tuple((j,-a) for j,a in row);rhs[i]=-rhs[i]
        key=row,rhs[i]
        if key in seen:continue
        seen.add(key);h.addRow(rhs[i],rhs[i],len(row),[j for j,w in row],[w for j,w in row])
    print(n,sector,word,'supported',len(use),'single-defect locations',len(rare),'rows',h.getNumRow(),flush=True)
    h.run();print('profile LP',h.getModelStatus(),flush=True)
    if h.getModelStatus()!=H.HighsModelStatus.kOptimal:return
    # One integral physical occurrence cannot split between distinct
    # location/event types, even if several positions share one type.
    for t in (0,1):
        yes=[j for j in rare if labs[use[j]][0][0]==t];no=[j for j in rare if j not in yes]
        h.changeColsBounds(len(no),np.array(no,dtype=np.int32),np.zeros(len(no)),np.zeros(len(no)))
        h.run();print('only','star' if t==0 else 'patch',h.getModelStatus(),flush=True)
        h.changeColsBounds(len(no),np.array(no,dtype=np.int32),np.zeros(len(no)),np.ones(len(no)))
if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2]),tuple(map(int,sys.argv[3])))
