"""Count complete aligned pitch lines and full junction classes at score 3647."""
from collections import Counter
from pathlib import Path
import json
from .rank44_faces import test,labels


def run(save=False):
    ns,A,b,M,bo,_,S,_=test(weighted=True,free=True,price_pure=True,cuts=False)
    A.append((list(S.items()),'>='));b.append(1)
    A.append((list(M.items()),'='));b.append(3647)
    # p0 on the last transition means no horizontal owned stub and
    # every junction marked. Horizontal orbit average times two counts
    # horizontal plus vertical complete profiles on junction lines.
    T={x:-2 for key,x in ns.items() if key[0]=='floorLine'
       and key[2][1]==labels(0,102,103,8)[1] and key[2][3][0]=='p0'}
    scale=10**12
    for name,obj,threshold in [('neg_lines',T,-6),('classes',S,6)]:
        path=Path(__file__).with_name(f'pitch_contacts_103_{name}.json')
        if save:
            from .side28_score import solve
            v,dual,_=solve(A,b,obj,ns,interior=True,bounds=bo)
            print(name,'numerical',v,flush=True)
            y={i:round(a*scale) for i,a in enumerate(dual) if round(a*scale)}
            for i in y:
                if A[i][1]=='<=':y[i]=max(0,y[i])
                if A[i][1]=='>=':y[i]=min(0,y[i])
        else:y=dict(json.loads(path.read_text()))
        rc=Counter({x:c*scale for x,c in obj.items()});upper=0
        for i,v in y.items():
            row,op=A[i];assert op=='=' or (v>=0 if op=='<=' else v<=0)
            upper+=b[i]*v
            for x,c in row:rc[x]-=c*v
        assert not any(bo.values())
        repair=103**2*sum(v for x,v in rc.items() if v>0 and x not in bo)
        upper+=repair
        assert upper<threshold*scale
        print(name,'integer upper numerator',upper,'scale',scale,'residual included',repair,
              'rows',len(A),flush=True)
        if save:path.write_text(json.dumps(sorted((i,v) for i,v in y.items() if v),separators=(',',':'))+'\n')


if __name__=='__main__':
    import sys
    run('--save' in sys.argv)
