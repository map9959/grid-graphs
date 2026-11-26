"""Search the small pooled dual for an orbit-integrality split certificate."""
from .repeating_patch_dual import polynomial,Q
from .patch_square import Counter,Path,json
from .square_dual_physical import trans,SYM


def data():
    n0,ns,A,b,obj=polynomial(2,3,2);j=(77-n0)//3
    rhs=[a+j*d+j*(j-1)//2*c for a,d,c in b]
    mu={}
    for (kind,atom),x in ns.items():
        p,*ev=atom
        # Reflection of a fine periodic coordinate is the corresponding
        # coordinate type of the reflected representative physical site.
        dim=77 if kind=='s' else 75;depth=6 if kind=='s' else 5
        def ix(i):return i if i<depth else 2*depth+3+i-dim if i>=dim-depth else depth+(i-depth)%3
        r,c=(next(i for i in range(dim) if ix(i)==v) for v in p)
        images=set()
        for g in range(8):
            pos=tuple(map(ix,trans(r,c,dim,g)))
            if kind=='p':images.add((pos,SYM[ev[0]][g]));continue
            f,nb,out=ev
            turn=lambda d:((2-d if g&4 else d)+g%4)%4
            images.add((pos,f,tuple(sorted((turn(d),w) for d,w in enumerate(nb))),-1 if out<0 else turn(out)))
        mu[x]=len(images)
    # Normalization bounds for aggregate probabilities, not probabilities per site.
    cap={}
    for (row,op),v in zip(A,rhs):
        if op=='=' and v>0 and all(w>0 for x,w in row):
            for x,w in row:cap[x]=min(cap.get(x,v),v//w+1)
    assert cap.keys()==mu.keys()
    return ns,A,rhs,obj,mu,cap


def run():
    import highspy as H
    ns,A,rhs,obj,mu,cap=data();cols=list(ns.values());ids={x:i for i,x in enumerate(cols)}
    h=H.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
    h.addVars(len(cols),[0.]*len(cols),[cap[x] for x in cols])
    h.changeColsCost(len(cols),list(range(len(cols))),[obj[x] for x in cols])
    for (row,op),b in zip(A,rhs):
        h.addRow(b if op!='<=' else -H.kHighsInf,b if op!='>=' else H.kHighsInf,
                 len(row),[ids[x] for x,w in row],[w for x,w in row])
    h.setMaximize()
    todo=[[]];tested=0;leaves=[]
    while todo:
        bounds=todo.pop();lo=Counter();hi=cap.copy()
        for x,t,sign in bounds:
            if sign:lo[x]=max(lo[x],Q(t,mu[x]))
            else:hi[x]=min(hi[x],Q(t,mu[x]))
        for x in cols:h.changeColBounds(ids[x],float(lo[x]),float(hi[x]))
        h.run();tested+=1
        if h.getModelStatus()==H.HighsModelStatus.kInfeasible:
            leaves.append((bounds,'infeasible'));continue
        assert h.getModelStatus()==H.HighsModelStatus.kOptimal
        s=h.getObjectiveValue();sol=h.getSolution()
        if s<2048-1e-7:
            leaves.append((bounds,s));continue
        def priority(x):
            v=mu[x]*sol.col_value[ids[x]]
            return round(abs(v-round(v)),6),-cap[x],-ids[x]
        x=max(cols,key=priority)
        if priority(x)[0]<1e-5:print('integer orbit counts in pooled relaxation at',s,'depth',len(bounds),flush=True);return
        t=int(mu[x]*sol.col_value[ids[x]])
        todo.extend([bounds+[(x,t+1,True)],bounds+[(x,t,False)]])
        if tested%200==0:print('tested',tested,'remaining',len(todo),'leaves',len(leaves),flush=True)
    print('candidate numerical split tree leaves',len(leaves));Path('target/pooled_77_leaves.json').write_text(json.dumps(leaves))


if __name__=='__main__':run()
