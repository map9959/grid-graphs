"""Lower-bound turn cost for any realization of the fractional chart's direction totals."""
from itertools import product
from collections import defaultdict,Counter
from fractions import Fraction as Q
from pathlib import Path
import json
from .skeleton_exit_chart import DIR,arrow_stage,model


def turn_lp(target,n=103,save=False):
    m=n//3+1
    # A profile chooses horizontal or vertical as its preferred axis.
    # Its cost is the realized incident edges OFF that axis. Min over
    # choices is exactly min(horizontal degree, vertical degree).
    # Symmetrize the root over the four corners; counts below are orbit sums.
    # Simpler unpooled version: the NW root realizes the same D4 totals.
    objs=[];rhs=[];rows=[];edge=defaultdict(list);bucket=defaultdict(list)
    stars=[]
    for i,j in product(range(m),repeat=2):
        ds=[s for s,(a,b) in enumerate(DIR) if 0<=i+a<m and 0<=j+b<m]
        local=[]
        for out in ([-1] if i==j==0 else ds):
            other=[s for s in ds if s!=out]
            for mask in range(1<<len(other)):
                inc=[s for l,s in enumerate(other) if mask>>l&1];axes=[*inc,*([out] if out>=0 else [])]
                hdeg=sum(s%2==0 for s in axes);v=len(objs);objs.append(min(hdeg,len(axes)-hdeg))
                local.append((v,1))
                if out>=0:
                    edge[i,j,out].append((v,1));bucket[arrow_stage(3*i,3*j,out,n,4,4)].append((v,1))
                for s in inc:
                    a,b=DIR[s];edge[i+a,j+b,(s+2)%4].append((v,-1))
        rows.append(local);rhs.append(1);stars.append(local)
    for row in edge.values():rows.append(row);rhs.append(0)
    for t,row in bucket.items():rows.append(row);rhs.append(target[t])
    path=Path(__file__).with_name('coarse_turn_103_dual.json');scale=4096
    if save:
        import highspy as H
        import numpy as np
        h=H.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
        h.setOptionValue('solver','ipm');h.setOptionValue('run_crossover','off')
        h.addVars(len(objs),np.zeros(len(objs)),np.full(len(objs),H.kHighsInf))
        h.changeColsCost(len(objs),np.arange(len(objs)),objs)
        for row,b in zip(rows,rhs):
            h.addRow(float(b),float(b),len(row),[v for v,_ in row],[t for _,t in row])
        h.run();assert h.getModelStatus()==H.HighsModelStatus.kOptimal
        raw=[round(t*scale) for t in h.getSolution().row_dual[len(stars):]]
    else:raw=json.loads(path.read_text())
    assert len(raw)==len(rows)-len(stars)
    # Site normalizations can absorb the worst residual among their
    # own profiles; no floating-point bound is used in the replay.
    dual=[Q(0)]*len(stars)+[Q(t,scale) for t in raw]
    excess=[-v for v in objs]
    for row,y in zip(rows,dual):
        for v,t in row:excess[v]+=t*y
    for i,local in enumerate(stars):dual[i]-=max(excess[v] for v,_ in local)
    lb=sum(y*b for y,b in zip(dual,rhs));assert lb>160
    if save:path.write_text(json.dumps(raw,separators=(',',':'))+'\n')
    return lb,len(objs)


if __name__=='__main__':
    occ=defaultdict(Counter)
    model(103,4,4,43,edge_floor=True,lines=True,faces=True,isolate_cut=True,arrow_data=occ)
    v={k:Q(z) for k,z in json.loads(Path(__file__).with_name('skeleton_exit_103_4_4_lines_faces_cut.json').read_text()).items()}
    target={k:sum(w*v.get(x,0) for x,w in row.items()) for k,row in occ.items()}
    import sys
    lb,count=turn_lp(target,save='--save' in sys.argv)
    print('checked',count,'junction profiles: exact dual lower > 160; physical upper 73')
