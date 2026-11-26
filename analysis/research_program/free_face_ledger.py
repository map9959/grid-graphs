"""Exact objective dual with no fixed off-count, component count, join rank or slack."""
from collections import Counter
import json
from pathlib import Path
from .rank44_faces import test


def certify(save=False):
    ns,A,b,M,bo,F,sink,ex=test(weighted=True,free=True,cuts=False)
    A.append((list(sink.items()),'>='));b.append(1)
    path=Path(__file__).with_name('free_face_ledger_103_dual.json')
    scale=10**12
    if save:
        from .side28_score import solve
        score,dual,_=solve(A,b,M,ns,interior=True,bounds=bo)
        print('numerical score',score,flush=True)
        y=[round(v*scale) for v in dual]
        assert len(y)==len(A)
        y={i:(max(0,v) if op=='<=' else min(0,v) if op=='>=' else v)
           for i,(v,(_,op)) in enumerate(zip(y,A)) if v}
    else:y=dict(json.loads(path.read_text()))
    rc=Counter({x:w*scale for x,w in M.items()});rhs=0
    for i,v in y.items():
        row,op=A[i]
        assert op=='=' or (v>=0 if op=='<=' else v<=0)
        rhs+=b[i]*v
        for x,w in row:rc[x]-=v*w
    assert not any(bo.values())
    repair=103**2*sum(v for x,v in rc.items() if x not in bo and v>0)
    ub=rhs+repair
    print('free F,C,j,X;',len(ns),'variables;',len(A),'rows; residual allowance',repair,
          'score upper numerator',ub,'gain upper numerator',ub-3605*scale,'scale',scale,flush=True)
    assert ub<3647*scale
    if save:path.write_text(json.dumps(sorted((i,v) for i,v in y.items() if v),separators=(',',':'))+'\n')


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--save',action='store_true')
    a=p.parse_args();certify(a.save)
