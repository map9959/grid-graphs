"""Price all rooted coarse-tree cuts against the sector chart's junction arrows."""
from collections import Counter,defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json,subprocess
from .skeleton_exit_chart import model,arrow_stage,tree_stage,exact_basic,DIR


def oracle(n,keys,parents=False):
    m=n//3+1;ids={k:i for i,k in enumerate(keys)};es=[]
    for i,j in product(range(m),repeat=2):
        for o,(a,b) in enumerate(DIR):
            v,t=i+a,j+b
            if 0<=v<m and 0<=t<m:
                es.append((i*m+j,v*m+t,ids[arrow_stage(3*i,3*j,o,n,4,4)]))
    p=subprocess.Popen(['target/skeleton_arborescence',*(['--parents'] if parents else [])],text=True,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    p.stdin.write(f'{m*m} {len(es)} {len(keys)}\n')
    for e in es:p.stdin.write('%d %d %d\n'%e)
    def run(weight):
        p.stdin.write(' '.join(map(str,weight))+'\n');p.stdin.flush()
        v=list(map(int,p.stdout.readline().split()))
        if parents:assert len(v)==m*m and v[0]==0
        else:assert sum(v)==m*m-1 and len(v)==len(keys)
        return v
    return p,run


def fit(z,run):
    import highspy as H
    h=H.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
    for b in [*z,1]:h.addRow(float(b),float(b),0,[],[])
    for i in range(len(z)):
        for s in (-1,1):h.addCol(1,0,H.kHighsInf,1,[i],[s])
    used=set();weights=[];cols=[];w=[0]*len(z)
    while True:
        v=run(w);assert tuple(v) not in used
        used.add(tuple(v));weights.append(w);cols.append(v)
        h.addCol(0,0,H.kHighsInf,len(z)+1,list(range(len(z)+1)),[*v,1]);h.run()
        assert h.getModelStatus()==H.HighsModelStatus.kOptimal
        sol=h.getSolution()
        if h.getObjectiveValue()<1e-7:break
        w=[round(t*10**8) for t in sol.row_dual[:-1]]
        mx=sum(t*s for t,s in zip(w,run(w)))
        gap=sum(t*s for t,s in zip(z,w))-mx
        if gap>0:return None,(w,mx,gap)
    A=[([(i,v[t]) for i,v in enumerate(cols) if v[t]],'=') for t in range(len(z))]
    A.append(([(i,1) for i in range(len(cols))],'='))
    val=exact_basic(A,[*z,1],dict(enumerate(sol.col_value[2*len(z):])))
    return [(w,val[i]) for i,w in enumerate(weights) if val.get(i)],None


def joint_fit(ns,A,b,obj,bounds,occ,keys,run,initial):
    """Column-generate the projected arborescence polytope inside the sector LP."""
    import highspy as H
    import numpy as np
    A=A+[(list(obj.items()),'=')];b=b+[3647]
    hdr=len(A);ids={x:i for i,x in enumerate(ns.values())};cols=list(ids)
    h=H.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
    h.addVars(len(ids),np.zeros(len(ids)),np.array([0 if x in bounds else H.kHighsInf for x in cols]))
    for (row,op),v in zip(A,b):
        h.addRow(v if op!='<=' else -H.kHighsInf,v if op!='>=' else H.kHighsInf,
                 len(row),[ids[x] for x,q in row],[q for x,q in row])
    for k in keys:
        row=occ[k];h.addRow(0,0,len(row),[ids[x] for x in row],[-v for v in row.values()])
    h.addRow(1,1,0,[],[])
    for i in range(len(keys)):
        for s in (1,-1):h.addCol(1,0,H.kHighsInf,1,[hdr+i],[s])
    ws=[];trees=[];seen=set()
    def put(w,v):
        if tuple(v) in seen:return False
        seen.add(tuple(v));ws.append(w);trees.append(v)
        h.addCol(0,0,H.kHighsInf,len(v)+1,list(range(hdr,hdr+len(v)+1)),[*v,1])
        return True
    for w in initial:put(w,run(w))
    h.setOptionValue('solver','ipm');h.setOptionValue('run_crossover','on')
    while True:
        h.run();assert h.getModelStatus()==H.HighsModelStatus.kOptimal
        sol=h.getSolution();err=h.getObjectiveValue()
        print('joint trees',len(ws),'remaining L1',err,flush=True)
        if err<1e-7:break
        h.setOptionValue('solver','simplex')
        w=[round(10**8*y) for y in sol.row_dual[hdr:-1]];v=run(w)
        if not put(w,v):raise RuntimeError('joint separation needs dual replay')
    full=list(cols)+[f'tree{i}' for i in range(len(ws))]
    hint=dict(zip(full,list(sol.col_value[:len(cols)])+list(sol.col_value[len(cols)+2*len(keys):])))
    for i,k in enumerate(keys):
        terms=[(x,-v) for x,v in occ[k].items()]+[(f'tree{j}',t[i]) for j,t in enumerate(trees) if t[i]]
        A.append((terms,'='));b.append(0)
    A.append(([(f'tree{i}',1) for i in range(len(ws))],'='));b.append(1)
    q=exact_basic(A,b,hint)
    for (row,op),rhs in zip(A,b):
        v=sum(t*q.get(x,0) for x,t in row)-rhs;assert {'=':v==0,'<=':v<=0,'>=':v>=0}[op]
    assert min(q.values())>=0 and not any(q.get(x,0) for x in bounds)
    return {x:q[x] for x in cols if q.get(x)},[(w,q[f'tree{i}']) for i,w in enumerate(ws) if q.get(f'tree{i}')]


if __name__=='__main__':
    import sys
    occ=defaultdict(Counter);edges=defaultdict(Counter)
    ns,A,b,obj,bounds,_=model(103,4,4,43,edge_floor=True,lines=True,faces=True,isolate_cut=True,arrow_data=occ,tree_data=edges)
    base=Path(__file__).with_name('skeleton_exit_103_4_4_lines_faces_cut.json')
    vals={x:Q(v) for x,v in json.loads(base.read_text()).items()}
    keys=sorted(occ);z=[sum(v*vals.get(x,0) for x,v in occ[k].items()) for k in keys]
    assert sum(z)==1224
    project={}
    for i,j in product(range(0,103,3),repeat=2):
        for o,(dy,dx) in enumerate(DIR):
            u,v=i+3*dy,j+3*dx
            if 0<=u<103 and 0<=v<103:
                k=arrow_stage(i,j,o,103,4,4)
                stage=tree_stage(j,min(i,u),103,4,4) if dy else tree_stage(i,min(j,v),103,4,4)
                assert project.setdefault(k,stage)==stage
    grouped=Counter()
    for k,s in zip(keys,z):grouped[project[k]]+=s
    assert grouped=={k:sum(v*vals.get(x,0) for x,v in c.items()) for k,c in edges.items()}
    path=base.with_name('skeleton_exit_rooted_mixture.json');p,run=oracle(103,keys)
    try:
        if '--joint' in sys.argv:
            initial=[w for w,_ in json.loads(path.read_text())] if path.exists() else [[0]*len(keys)]
            vals,mix=joint_fit(ns,A,b,obj,bounds,occ,keys,run,initial)
            z=[sum(v*vals.get(x,0) for x,v in occ[k].items()) for k in keys]
        elif '--save' in sys.argv:
            mix,sep=fit(z,run)
            if sep:
                print('exact separation: weights, maximum on trees, excess',sep);sys.exit()
        else:mix=[(w,Q(v)) for w,v in json.loads(path.read_text())]
        s=[Q(0)]*len(z)
        for w,v in mix:
            assert v>0
            for i,a in enumerate(run(w)):s[i]+=v*a
        assert s==z and sum(v for _,v in mix)==1
        if '--joint' in sys.argv:base.write_text(json.dumps({x:str(v) for x,v in vals.items()},sort_keys=True,separators=(',',':'))+'\n')
        if '--save' in sys.argv or '--joint' in sys.argv:path.write_text(json.dumps([(w,str(v)) for w,v in mix],separators=(',',':'))+'\n')
        print(len(edges),'edge and',len(keys),'outgoing direction histograms verified by exact mixture of',len(mix),
              'NW-rooted physical coarse trees of 1224 edges')
    finally:p.stdin.close();assert p.wait()==0
