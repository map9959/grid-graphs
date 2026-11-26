"""Finite score-293 decision for the r28 model. Replay uses only stdlib."""
from fractions import Fraction as Q
from collections import Counter
from pathlib import Path
import json
from .repeating_patch_dual import build
from .patch_square import MASKS,SYM,trans


def solve(A,b,obj,names,interior=False,bounds=None):
    import highspy as H
    import numpy as np
    h=H.Highs()
    h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
    if interior:
        h.setOptionValue('solver','ipm');h.setOptionValue('run_crossover','on' if interior=='cross' else 'off')
    cols=list(names.values());ids={x:i for i,x in enumerate(cols)}
    h.addVars(len(cols),np.zeros(len(cols)),np.full(len(cols),H.kHighsInf))
    if bounds:
        h.changeColsBounds(len(bounds),[ids[x] for x in bounds],np.zeros(len(bounds)),list(bounds.values()))
    h.changeColsCost(len(cols),np.arange(len(cols)),[obj.get(x,0) for x in cols])
    for (row,op),v in zip(A,b):
        h.addRow(v if op!='<=' else -H.kHighsInf,v if op!='>=' else H.kHighsInf,
                 len(row),[ids[x] for x,w in row],[w for x,w in row])
    h.setMaximize();h.run()
    assert h.getModelStatus()==H.HighsModelStatus.kOptimal
    s=h.getSolution()
    return h.getObjectiveValue(),s.row_dual,dict(zip(cols,s.col_value))


def run(replay):
    names,A,b,obj=build(2,28,3,'r28')
    path=Path(__file__).with_name('side28_score_r28.json')
    if replay:
        typ,raw=json.loads(path.read_text())
        v={k:Q(z) for k,z in raw.items()}
    else:
        score,y,p=solve(A,b,obj,names)
        print('numerical candidate',score,flush=True)
        typ='dual' if score<293-1e-6 else 'primal'
        raw=({str(i):a for i,a in enumerate(y)} if typ=='dual' else p)
        v={k:Q(float(z)).limit_denominator(1000000) for k,z in raw.items() if abs(z)>1e-9}
    if typ=='primal':
        assert min(v.values())>=0
        for (row,op),rhs in zip(A,b):
            gap=sum(w*v.get(x,0) for x,w in row)-rhs
            assert {'=':gap==0,'<=':gap<=0,'>=':gap>=0}[op]
        score=sum(w*v.get(x,0) for x,w in obj.items());assert score>=293
        print('exact feasible score',score,'rows',len(A))
        # Mix with the empty selected set to attain exactly 293. Both
        # overlap origins are singleton fine types; the empty set gives
        # this particular nonempty event probability zero on both sides.
        weight=Q(293)/score
        event=(0,0,0,0,1,1)
        def axis(t):
            return t if t<5 else 13-26+t if t>=21 else 5+(t-5)%3
        marg=[]
        for j,start in [(3,1),(4,0)]:
            pos=[tuple(map(axis,trans(1,j,26,g))) for g in range(8)]
            masses={m:v.get(names['p',min(zip(pos,SYM[m]))],0) for m in MASKS}
            assert sum(masses.values())==1
            marg.append(weight*sum(q for m,q in masses.items() if
                         tuple(m>>(3*r+c)&1 for r in range(3) for c in (start,start+1))==event))
        assert marg[0]!=marg[1]
        print('exact score 293 mixture weight',weight,'strip overlap 00/00/11 probabilities',*marg)
    else:
        residual=Counter(obj);score=Q(0)
        for k,q in v.items():
            row,op=A[int(k)]
            assert op=='=' or (q>=0 if op=='<=' else q<=0)
            score+=q*b[int(k)]
            for x,w in row:residual[x]-=w*q
        # Positive residual could be repaired, but no allowance is assumed here.
        assert max(residual.values())<=0
        print('exact upper',score,'columns',len(names))
        assert score<293
    if not replay:path.write_text(json.dumps([typ,{k:str(z) for k,z in v.items()}],separators=(',',':'))+'\n')


if __name__=='__main__':
    import sys
    run('--replay' in sys.argv)
