"""Solver-free side-109 replay: pooled core plus integer full-width path bound."""
import json
import subprocess
from fractions import Fraction as Q
from pathlib import Path
from .seven_threshold import model,replay
from .six_joint_replay import projected
from .thirteen_local import overlaps

def upper():
    _,A,b,obj,labels=model(13)
    for row in overlaps(labels):A.append((row,'='));b.append(0)
    blocks,yy,cc,budget=json.loads(Path(__file__).with_name('thirteen_upper_109.json').read_text())
    assert blocks==[[0,9],[4,9]] and type(budget)==int
    labs={(o,h,r-o,m):x for o,H in blocks for (h,r,m),x in labels.items() if o<=r<o+H-2}
    y={int(i):Q(q) for i,q in yy.items()};cost={tuple(k):v for k,v in cc}
    assert all(0<=i<len(A) for i in y) and all(type(v)==int for v in cost.values())
    assert cost.keys()<=labs.keys()
    assert max(projected(A,b,obj,labs,y,{k:Q(v,10**8) for k,v in cost.items()}).values())<=0
    inp=' '.join(str(cost.get((o,h,r,m),0)) for o,_ in blocks for h in range(25) for r in range(7) for m in range(512))
    res=subprocess.run(['target/thirteen_price',str(budget)],input=inp,text=True,capture_output=True,check=True)
    price,visits=map(int,res.stdout.split());ub=sum(q*b[i] for i,q in y.items())-Q(price,10**8)
    print('replayed thirteen-row dual',ub,'=',float(ub),'retained arc visits',visits)
    assert ub<4094
    return ub

if __name__=='__main__':
    lower=replay(13);bound=upper();assert lower<=bound
