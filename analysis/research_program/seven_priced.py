"""Discover seven-row flows near the face exposed by the inherited four-row prices."""
from .seven_threshold import *
from .six_joint_replay import projected
from .redistributed_transfer import data

def priced(epsilon,iterations=1,interior=False,sparse=False):
    from .side28_score import solve
    from .all_pinned_sites import primal
    from math import inf
    ns,A,b,obj,labels=model()
    keys=list(data(109,0,ns,{})[0])
    yy=json.loads(file.with_name('full_top_109.json').read_text())[1]
    y={int(i):Q(w) for i,w in yy.items() if int(i)<len(A)}
    costs={k:Q(yy.get(str(len(A)+i),0)) for i,k in enumerate(keys)}
    rc=projected(A,b,obj,labels,y,costs)
    # Divide a pooled variable's reduced cost among linked events so the
    # sum along any feasible path mixture accounts for it exactly once.
    freq=Counter(labels.values())
    cst={k:float(costs.get(k,0)-rc[x]/freq[x]) for k,x in labels.items()}
    # Price backward at all seven-row states. Reuse stationary transition
    # tables and event costs at repeated phases; screen arcs by path regret.
    import numpy as np
    hmap=lambda j:axis(j-2,107) if j>=2 else -1
    @lru_cache(None)
    def layer(states):
        src=[];dst=[];cols=[];dest={};ms=[]
        for i,(a,b,p) in enumerate(states):
            for c in range(128):
                q=move(b,p,c)
                if q is None:continue
                d=b,c,q
                src.append(i);cols.append(c);dst.append(dest.setdefault(d,len(dest)));ms.append(masks(a,b,c))
        return tuple(dest),np.array(src),np.array(dst),np.array(cols),np.array(ms)
    # Canonical ordering makes eventual layer identical, even if the first
    # exploration order changes. Remap destinations to canonical indices.
    @lru_cache(None)
    def block(st):
        ds,s,d,c,m=layer(st);nxt=tuple(sorted(ds));idx={v:i for i,v in enumerate(nxt)}
        return nxt,s,np.array([idx[v] for v in ds])[d],c,m
    @lru_cache(None)
    def weighted(st,h):
        nxt,s,d,c,ms=block(st)
        if h==-1:return np.zeros(len(s))
        lut=np.zeros((5,512))
        for r in range(5):
            for m in MASKS:lut[r,m]=cst[h,r,m]
        return lut[np.arange(5),ms].sum(axis=1)
    st=(start,);blocks=[]
    for j in range(109):
        nxt,s,d,c,m=block(st);blocks.append((st,nxt,s,d,c));st=nxt
    # Add the known sparse witness so every discovery problem is feasible.
    pp,old=json.loads(file.read_text());prior=defaultdict(set)
    for j,(a,b0),part,c,_ in old:prior[j].add(((a,b0,tuple(part)),c))
    names0,A0,b0=ns,A,b
    rhs0=float(sum(w*b[i] for i,w in y.items()));center=cst.copy();bestupper=inf;radius=.2
    yc=np.array([float(y.get(i,0)) for i in range(len(A0))])
    resume=Path('target/seven_interior_candidate.json' if interior else 'target/seven_dual_candidate.json')
    if sparse:resume=Path('target/seven_sparse_candidate.json')
    if interior and not resume.exists() and Path('target/seven_dual_candidate.json').exists():
        resume.write_bytes(Path('target/seven_dual_candidate.json').read_bytes())
    if resume.exists():
        yp,cp=json.loads(resume.read_text());yc=np.array(yp);center=cst=dict(zip(labels,cp));rhs0=np.dot(yc,b0)
    weights0=None;yr=yc.copy()
    for it in range(iterations):
      weighted.cache_clear()
      ws=[weighted(st,hmap(j)) for j,(st,*_) in enumerate(blocks)]
      def sweep(weights):
        fw=[np.array([0.])]
        for (st,nxt,s,d,c),w in zip(blocks,weights):
            v=np.full(len(nxt),inf);np.minimum.at(v,d,fw[-1][s]+w);fw.append(v)
        return fw
      if weights0 is not None:
        base_rhs=np.dot(yc,b0);choice=(bestupper,0)
        for a in (1,.5,.25,.125,.0625,.03125,.015625,.0078125):
            z=[u+a*(v-u) for u,v in zip(weights0,ws)]
            u=base_rhs+a*(rhs0-base_rhs)-min(sweep(z)[-1])
            if u<choice[0]-1e-9:choice=(u,a)
        ub,a=choice
        if a:
            bestupper=ub;yc=yc+a*(yr-yc);center={k:center[k]+a*(cst[k]-center[k]) for k in labels}
            weights0=[u+a*(v-u) for u,v in zip(weights0,ws)]
            resume.write_text(json.dumps([list(yc),list(center.values())]))
        print('line search',a,'best upper',bestupper,flush=True)
        if bestupper<4096.9999:return
      fw=sweep(ws);layers=[]
      for j,(st,nxt,s,d,c) in enumerate(blocks):
        layers.append((st,nxt,s,d,c,ws[j]))
      best=min(fw[-1]);upper=rhs0-best
      print(it,'full priced minimum',best,'upper candidate',upper,flush=True)
      if weights0 is None:
        bestupper=upper;weights0=ws
      if upper<4096.99999:return
      bw=np.zeros(len(blocks[-1][1]));links=defaultdict(list);flow=defaultdict(list);nn=0
      A=A0.copy();b=b0.copy();ns=names0.copy();objective=obj.copy();bounds={}
      for j in reversed(range(109)):
        st,nxt,s,d,c,w=layers[j];z=w+bw[d];bw=np.full(len(st),inf);np.minimum.at(bw,s,z)
        for i in np.flatnonzero(fw[j][s]+z<=best+(epsilon if not it else .03)+1e-9):prior[j].add((st[s[i]],int(c[i])))
        for i,(state,col) in enumerate(sorted(prior[j])):
            a,v,part=state;dest=v,col,move(v,part,col);x=f'z{j}_{i}';ns['arc',j,state,col]=x;nn+=1
            flow[j,state].append((x,1))
            if j<108:flow[j+1,dest].append((x,-1))
            if j>=2:
                for r,m in enumerate(masks(a,v,col)):links[hmap(j),r,m].append((x,1))
      print('screened arcs',nn,flush=True)
      for i,(k,x) in enumerate(labels.items()):
        terms=links[k]+[(x,-1)]
        if iterations>1:
            for sign in (-1,1):
                art=f'u{i}_{sign}';ns['box',i,sign]=art;terms.append((art,sign))
                mult=30 if 8<=k[0]<=10 else 1
                objective[art]=sign*center[k]-(.0001 if sparse else radius)/mult
                if sparse:bounds[art]=.015*mult
        A.append((terms,'='));b.append(0)
      for k,cs in flow.items():A.append((cs,'='));b.append(int(k==(0,start)))
      val,raw,v=solve(A,b,objective,ns,interior=interior,bounds=bounds);print('restricted objective',val,flush=True)
      if iterations==1 and val>=4097-1e-8:
        if interior:
            sub={k:x for k,x in ns.items() if v[x]>1e-7}
            allowed=set(sub.values());thin=[([(x,w) for x,w in row if x in allowed],op) for row,op in A]
            _,_,v=solve(thin,b,obj,sub);p=primal(thin,b,v)
        else:p=primal(A,b,v)
        save(p,ns,file.stem);assert replay()>=4097
      cst=dict(zip(labels,raw[len(A0):]));yr=np.array(raw[:len(A0)]);rhs0=np.dot(yr,b0)
      if sparse:
        rem=projected(A0,b0,obj,labels,dict(enumerate(yr)),cst)
        refl=lambda m:((m&73)<<2)|(m&146)|((m&292)>>2)
        mirror={axis(j,107):axis(106-j,107) for j in range(107)}
        cp={k:cst[k]-min(rem[x],0)/freq[x] for k,x in labels.items()}
        cst={k:(q+cp[mirror[k[0]],k[1],refl(k[2])])/2 for k,q in cp.items()}

if __name__=='__main__':
    import sys
    priced(float(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 1,'--ipm' in sys.argv,'--sparse' in sys.argv)
