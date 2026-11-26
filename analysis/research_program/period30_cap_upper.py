"""Try a physical period-30 local dual for n=49+30j. Every RHS is counted symbolically."""
from fractions import Fraction as Q
from .repeating_patch_dual import build,verify
from .side28_score import solve
from collections import Counter
from pathlib import Path
import json,hashlib


def model(d):
    n=49;period=30
    names,A,b,obj=build(d,n,period)
    inv={x:k for k,x in names.items()};rhs=[]
    for (row,op),v in zip(A,b):
        if v==0 or op!='=':rhs.append((v,0,0));continue
        kind,atom=inv[row[0][0]]
        depth=d+(4 if kind=='s' else 3);side=n-(0 if kind=='s' else 2)
        def axis(t):
            if t<depth or t>=depth+period:return 1,0
            return (side-2*depth+period-1-(t-depth))//period,1
        a,h=axis(atom[0][0]);c,k=axis(atom[0][1])
        assert a*c==v and all(w>0 for x,w in row)
        rhs.append((v,a*k+c*h,h*k))
    return names,A,rhs,obj


def run(d,j,replay=False):
    names,A,rhs,obj=model(d)
    digest=hashlib.sha256(repr((A,rhs,sorted(obj.items()))).encode()).hexdigest()
    path=Path(__file__).with_name(f'period30_cap_d{d}.json')
    if replay:
        sig,p=json.loads(path.read_text());assert sig==digest
        y={i:Q(v) for i,v in p}
    else:
        b=[v+h*j+k*j*j for v,h,k in rhs]
        opt,yy,_=solve(A,b,obj,names);print('numerical horizon objective',opt,flush=True)
        y={i:Q(round(v*10**8),10**8) for i,v in enumerate(yy) if round(v*10**8)}
        norm={};res=Counter(obj)
        for i,((row,op),c) in enumerate(zip(A,rhs)):
            if op=='=' and c[0]>0:
                for x,w in row:norm[x]=(i,w)
            z=y.get(i,0)
            if op=='>=':assert z<=0
            for x,w in row:res[x]-=z*w
        for x,z in res.items():
            if z>0:
                i,w=norm[x];y[i]=y.get(i,0)+z/w
    assert verify(A,obj,y)<=0
    coeff=tuple(sum(v*rhs[i][t] for i,v in y.items()) for t in range(3))
    target=(851,1013,300) # k=16+10j
    assert all(3*(16+10*i)**2+5*(16+10*i)+(3*(16+10*i)-13)//10==
               sum(v*i**t for t,v in enumerate(target)) for i in range(3))
    print('verified',len(names),'columns; excess coefficients in j:',*[str(c-v) for c,v in zip(coeff,target)],flush=True)
    if not replay:path.write_text(json.dumps([digest,[[i,str(v)] for i,v in sorted(y.items())]],separators=(',',':'))+'\n')


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--depth',type=int,default=2);p.add_argument('--horizon',type=int,default=2)
    p.add_argument('--replay',action='store_true')
    args=p.parse_args();run(args.depth,args.horizon,args.replay)
