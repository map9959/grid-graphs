"""Joint seven-row side-109 forest-flow search and exact rational replay."""
from functools import lru_cache
from .six_joint_lp import core,axis,Q,Path,json,Counter,defaultdict
from .six_support import trans,MASKS,SYM
from .top6_sparse import old_support,save

start=(0,0,tuple(range(7)))
file=Path(__file__).with_name('seven_lower_109.json')

def model(height=7):
    ns,A,b,obj,labels=model(height-1) if height>=12 else core()
    if height>=11:
        # Split the next boundary position and its reflection on BOTH axes.
        # Each new variable is a sum over its finer Cartesian bucket, not
        # a probability tied to all physical positions in that bucket.
        fine=lambda t:fine_axis(t,height)
        old=lambda t:fine_axis(t,height-1)
        parent,child,prefix={11:('p','fine','f'),12:('fine','finer','g'),13:('finer','fine13','h'),14:('fine13','fine14','i'),15:('fine14','fine15','j')}[height]
        reps={fine(t):t for t in range(107)};pieces=defaultdict(dict);labels={}
        for fi,i in reps.items():
          for fj,j in reps.items():
            pos=[trans(i,j,107,g) for g in range(8)]
            coarse=[(old(a),old(c)) for a,c in pos]
            detail=[(fine(a),fine(c)) for a,c in pos]
            for m in MASKS:
                x=ns[parent,min(zip(coarse,SYM[m]))]
                key=(child,min(zip(detail,SYM[m])))
                z=ns.setdefault(key,prefix+str(len(ns)))
                pieces[old(i),old(j),m][fi,fj]=(z,x)
                if i<height-2:labels[fj,i,m]=z
        eq=set();mult=Counter(fine(i) for i in range(107));norms=defaultdict(Counter)
        for (a,bj,m),x in labels.items():norms[a,bj][x]+=1
        for vals in pieces.values():
            counts=Counter(z for z,x in vals.values());xs={x for z,x in vals.values()};assert len(xs)==1
            counts[xs.pop()]-=1;eq.add(tuple(sorted(counts.items())))
        for terms in sorted(eq):A.append((terms,'='));b.append(0)
        for (a,bj),cs in sorted(norms.items()):A.append((tuple(cs.items()),'='));b.append(mult[a])
        return ns,A,b,obj,labels
    for r in range(4,height-2):
      for j in range(107):
        pos=[tuple(axis(t,107) for t in trans(r,j,107,g)) for g in range(8)]
        for m in MASKS:
            x=ns['p',min(zip(pos,SYM[m]))]
            assert labels.setdefault((axis(j,107),r,m),x)==x
    return ns,A,b,obj,labels

def fine_axis(j,height):
    if height>=15 and j in (12,94):return 27 if j==12 else 28
    if height>=14 and j in (11,95):return 25 if j==11 else 26
    if height>=13 and j in (10,96):return 23 if j==10 else 24
    if height>=12 and j in (9,97):return 21 if j==9 else 22
    return (19 if j==8 else 20 if j==98 else axis(j,107)) if height>=11 else axis(j,107)

@lru_cache(None)
def move(b,part,c):
    H=len(part);p=list(part)+list(range(H,2*H))
    def root(x):
        while p[x]!=x:x=p[x]
        return x
    for i in range(H):
        for u,v,on in ((i,i+H,((b|c)>>i)&1),(i+H,i+H+1,i<H-1 and ((c|c>>1)>>i)&1)):
            if on:
                a,z=root(u),root(v)
                if a==z:return
                p[a]=z
    roots=[root(i) for i in range(H,2*H)]
    return tuple(roots.index(z) for z in roots)

def spread(x):return (x&1)+((x&2)<<2)+((x&4)<<4)
def masks(a,b,c,height=7):
    return [spread(a>>r)+2*spread(b>>r)+4*spread(c>>r) for r in range(height-2)]

def pathspec(height):
    stems={6:'six',7:'seven',8:'eight',9:'nine',10:'ten',11:'eleven',12:'twelve',13:'thirteen',14:'fourteen',15:'fifteen'}
    return ((0,0,tuple(range(height))),file.with_name(stems[height]+'_lower_109.json'),
            file.with_name(stems[height-1]+'_lower_109.json'))

def generate(fixed,depth=4,face=False,height=7,interior=False):
    from .side28_score import solve
    from .all_pinned_sites import primal
    start,file,prev=pathspec(height)
    ns,A,b,obj,labels=model(height)
    pp=json.loads(prev.read_text())[0]
    keep=set(pp) if fixed else set(pp)|old_support()
    if not fixed and height>=9:
        for stem in ('six','seven','eight','nine')[:height-7]:
            keep.update(json.loads(file.with_name(stem+'_lower_109.json').read_text())[0])
    if not fixed and file.exists():keep.update(json.loads(file.read_text())[0])
    original_keep=keep.copy()
    parents={z:x for (terms,_),bb in zip(A,b) if bb==0 and any(z.startswith('f') for z,w in terms)
             for x,sgn in terms if sgn==-1 for z,w in terms if w>0}
    keep.update(z for z,x in parents.items() if x in original_keep)
    for level,prefix in ((12,'g'),(13,'h'),(14,'i'),(15,'j')):
        if height<level:break
        immediate={z:x for (terms,_),bb in zip(A,b) if bb==0 and any(z.startswith(prefix) and w>0 for z,w in terms)
                   for x,sgn in terms if sgn==-1 for z,w in terms if w>0}
        if fixed and level==height:keep=set(pp)
        keep.update([z for z,x in immediate.items() if x in keep])
    if face:
        from .six_joint_replay import projected
        from .redistributed_transfer import data
        keys=list(data(109,0,ns,{})[0])
        yy=json.loads(file.with_name('full_top_109.json').read_text())[1]
        y={int(i):Q(w) for i,w in yy.items() if int(i)<len(A)}
        costs={k:Q(yy.get(str(len(A)+i),0)) for i,k in enumerate(keys)}
        rc=projected(A,b,obj,labels,y,costs)
        assert max(rc.values())<=0
        keep.update(x for x in labels.values() if not rc[x])
    broad={(r,m) for (h,r,m),x in labels.items() if x in keep}
    def allowed(h,r,m):
        if labels.get((h,r,m)) in keep:return True
        if fixed:return False
        if depth<0:return (r,m) in broad if r < -depth else True
        return r>=depth
    @lru_cache(None)
    def choices(h,r,a,v):
        return {c for c in range(8) if allowed(h,r,spread(a)+2*spread(v)+4*spread(c))}
    @lru_cache(None)
    def options(h,a,v):
        cols=[0]
        for r in range(height-2):
            valid=choices(h,r,(a>>r)&7,(v>>r)&7)
            cols=[x for c in cols for k in (range(8) if not r else (0,4)) for x in [c|(k<<r)] if (x>>r)&7 in valid]
        return [(c,[(h,r,m) for r,m in enumerate(masks(a,v,c,height))]) for c in cols]
    # Necessary support for the first two columns of the first patch.
    @lru_cache(None)
    def initial(j,b,c):
        for r in range(height-2):
            a0=(b>>r)&7 if j else (c>>r)&7
            if not any(choices(0,r,a0,v) for v in (((c>>r)&7,) if j else range(8))):return False
        return True
    states={start};layers=[]
    for j in range(109):
        arcs=[];nxt=set()
        for s in sorted(states):
            a,v,p=s
            for c,ev in (options(fine_axis(j-2,height),a,v) if j>=2 else ((c,[]) for c in range(1<<height) if initial(j,v,c))):
                q=move(v,p,c)
                if q is not None:
                    d=(v,c,q);arcs.append((s,c,d,ev));nxt.add(d)
        states=nxt;layers.append(arcs)
        if fixed and not states:
            print('no supported forest prefix reaches column',j,'(zero-based)');return False
    for j in reversed(range(109)):
        layers[j]=[a for a in layers[j] if a[2] in states];states={a[0] for a in layers[j]}
    print('support arcs',sum(map(len,layers)),flush=True)
    if not states:
        print('no complete supported path');return False
    if fixed:
        seen={k for layer in layers for _,_,_,ev in layer for k in ev}
        if height>=12:
            oh={fine_axis(j,height):fine_axis(j,height-1) for j in range(107)}
            seen_old={(oh[h],r,m) for h,r,m in seen}
            oldlabels=model(height-1)[-1]
            absent=[(k,pp[x]) for k,x in oldlabels.items() if x in pp and k not in seen_old]
            if absent:
                print('fixed height',height-1,'point impossible: unreachable required event',absent[0]);return False
        else:
            coarse_h={fine_axis(j,height):axis(j,107) for j in range(107)}
            seen_coarse={(coarse_h[h],r,m) for h,r,m in seen}
            missing=[(k,pp[parents.get(x,x)]) for k,x in labels.items() if k[1]<8 and k[0]<19 and parents.get(x,x) in pp and k not in seen_coarse]
            if missing:
                print('fixed pooled point impossible: required event unreachable on every supported full-width path:',missing[0]);return False
    flow=defaultdict(list);links=defaultdict(list)
    if fixed:
        for x in ns.values():
            if x not in (immediate if height>=12 else parents):A.append(([(x,1)],'='));b.append(Q(pp.get(x,0)))
    for j,arcs in enumerate(layers):
        for i,(s,c,d,ev) in enumerate(arcs):
            x=f'z{j}_{i}';ns['arc',j,s,c]=x
            flow[j,s].append((x,1))
            if j<108:flow[j+1,d].append((x,-1))
            for k in ev:links[k].append((x,1))
    for k,x in labels.items():
        A.append((links[k]+[(x,-1)],'='));b.append(0)
    for k,cs in flow.items():A.append((cs,'='));b.append(int(k==(0,start)))
    val,_,v=solve(A,b,obj,ns,interior=interior);print('numerical score',val,flush=True)
    if interior:
        sub={k:x for k,x in ns.items() if v[x]>1e-8}
        support=set(sub.values())
        A=[([(x,w) for x,w in cs if x in support],op) for cs,op in A]
        _,_,v=solve(A,b,obj,sub)
    p=primal(A,b,v);save(p,ns,file.stem)
    replay(height)

def replay(height=7):
    start,file,_=pathspec(height)
    ns,A,b,obj,labels=model(height);pp,arcs=json.loads(file.read_text())
    p={x:Q(v) for x,v in pp.items()};assert min(p.values())>=0 and p.keys()<=set(ns.values())
    for (cs,op),bb in zip(A,b):
        z=sum(w*p.get(x,0) for x,w in cs)-bb
        assert {'=':z==0,'<=':z<=0,'>=':z>=0}[op]
    bal=Counter();em=Counter()
    for j,(a,v),part,c,w in arcs:
        q=Q(w);assert q>0 and 0<=j<109 and 0<=c<1<<height and len(part)==height
        part=tuple(part);d=move(v,part,c);assert d is not None
        bal[j,(a,v,part)]+=q
        if j<108:bal[j+1,(v,c,d)]-=q
        if j>=2:
            for r,m in enumerate(masks(a,v,c,height)):em[fine_axis(j-2,height),r,m]+=q
    assert bal.pop((0,start))==1 and not any(bal.values())
    assert em.keys()<=labels.keys() and all(em[k]==p.get(x,0) for k,x in labels.items())
    score=sum(w*p.get(x,0) for x,w in obj.items())
    print('height',height,'exact score',score,'positive arcs',len(arcs),'phase totals',len(labels))
    return score

if __name__=='__main__':
    import sys
    height=15 if '--fifteen' in sys.argv else 14 if '--fourteen' in sys.argv else 13 if '--thirteen' in sys.argv else 12 if '--twelve' in sys.argv else 11 if '--eleven' in sys.argv else 10 if '--ten' in sys.argv else 9 if '--nine' in sys.argv else 8 if '--eight' in sys.argv else 7
    if '--replay' in sys.argv:replay(height)
    else:generate('--fixed' in sys.argv,int(sys.argv[-1]) if sys.argv[-1].lstrip('-').isdigit() else 4,'--face' in sys.argv,height,'--ipm' in sys.argv)
