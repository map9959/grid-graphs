"""Check a nonnegative polynomial primal ray for the repeating-dual ansatz."""
from collections import Counter
from fractions import Fraction as Q
import subprocess
from .repeating_patch_dual import polynomial,lpterms


def primal(A,rhs,obj):
    text='max: '+lpterms(obj)+';\n'+''.join(lpterms(dict(c))+f' {o} {b};\n' for (c,o),b in zip(A,rhs))
    res=subprocess.run(['lp_solve','-presolve'],input=text,text=True,capture_output=True,check=True)
    vals={x:Q(y) for s in res.stdout.splitlines() if len(s.split())==2 for x,y in [s.split()] if x.startswith('x') and x[1:].isdigit()}
    support={x for x,v in vals.items() if v>Q(1,10**8)}
    piv={}
    for (c,o),b in zip(A,rhs):
        if o!='=' and abs(sum(w*vals[x] for x,w in c)-b)>Q(1,1000):continue
        row={x:Q(w) for x,w in c if x in support};v=Q(b)
        while row:
            x=min(row,key=lambda x:int(x[1:]));z=row.pop(x)
            if x not in piv:
                piv[x]=({y:w/z for y,w in row.items()},v/z);break
            p,k=piv[x];v-=z*k
            for y,w in p.items():
                row[y]=row.get(y,0)-z*w
                if not row[y]:del row[y]
    vals={x:v.limit_denominator(10000) if x in support else 0 for x,v in vals.items()}
    for x in sorted(piv,key=lambda x:-int(x[1:])):
        p,b=piv[x];vals[x]=b-sum(w*vals[y] for y,w in p.items())
    assert min(vals.values())>=0
    for (c,o),b in zip(A,rhs):
        v=sum(w*vals[x] for x,w in c)
        assert (v==b if o=='=' else v>=b if o=='>=' else v<=b)
    return sum(v*vals[x] for x,v in obj.items()),vals


def run(d,period):
    n0,names,A,rhs,obj=polynomial(d,period)
    costs=[]
    for r in range(3):
        cost,x=primal(A,[row[r] for row in rhs],obj);costs.append(cost)
        print("binomial term",r,"value",cost,"positive events",sum(v>0 for v in x.values()),flush=True)
    a,b,c=costs
    n2=c/18
    linear=(b-3*(2*n0+3)*n2)/3
    print("pooled primal polynomial",n2,linear,a-n2*n0**2-linear*n0,"from n",n0)


if __name__=='__main__':
    import sys
    run(*map(int,sys.argv[1:]))
