"""Unrestricted overlap dual with periodic bulk and bounded boundary corrections."""
from collections import Counter,defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib,json,subprocess
from .patch_square import relaxation,lpterms


def build(d,n,period,strip=False):
    names,rows,obj=relaxation(n,d+4,pooled=d,period=period,strip_cut=strip)
    matrix=[];rhs=[]
    for c,op,b in rows:matrix.append((c,op));rhs.append(b)
    return names,matrix,rhs,obj


def polynomial(d,period=1,residue=2,strip=False):
    # Once the bulk is wider than four sites, a fine type determines
    # the pooled locations of all constraints touching it. Only the
    # multiplicities in its normalization can depend on side.
    assert period in (1,3)
    n0=2*(d+4)+period+4
    while n0%3!=residue:n0+=1
    names,A,b,obj=build(d,n0,period,strip)
    rhs=[b]
    for n in [n0+3,n0+6,n0+9]:
        ns,M,y,c=build(d,n,period,strip)
        assert (ns,M,c)==(names,A,obj)
        rhs.append(y)
    coeff=[]
    for a,b,c,e in zip(*rhs):
        dd=c-2*b+a
        assert e-3*c+3*b-a==0
        coeff.append((a,b-a,dd))
    # Check symbolic Newton coefficients from the independent 1D counting
    # formula: (u+U*j)(v+V*j), j=(n-n0)/3. Only normalization rows and
    # a fixed corner-sink requirement have a nonzero right-hand side.
    inv={v:k for k,v in names.items()}
    for ((row,op),cc) in zip(A,coeff):
        if cc==(0,0,0):continue
        if op=='>=':
            assert cc==(1,0,0)
            continue
        assert op=='=' and all(w>0 for x,w in row)
        cell=inv[row[0][0]]; s=(n0 if cell[0]=='s' else n0-2)
        depth=(d+4 if cell[0]=='s' else d+3)
        def count(index):
            if not depth<=index<depth+period:return 1,0
            k=index-depth
            return (s-2*depth+period-1-k)//period,3//period
        pos=cell[1][0];u,U=count(pos[0]);v,V=count(pos[1])
        assert cc==(u*v,u*V+U*v+U*V,2*U*V)
    return n0,names,A,coeff,obj


def filename(d,period,residue,strip=False):
    return Path(__file__).with_name(f'repeating_patch_dual_{d}'+(f'_p{period}' if period!=1 else '')+
                                    (f'_r{residue}' if residue!=2 else '')+('_strip_'+strip if isinstance(strip,str) else '_strip' if strip else '')+'.json')


def replay(d,period,residue=2,strip=False):
    n0,names,A,coeff,obj=polynomial(d,period,residue,strip)
    path=filename(d,period,residue,strip)
    digest,pairs=json.loads(path.read_text())
    assert digest==hashlib.sha256(repr((A,coeff,sorted(obj.items()))).encode()).hexdigest()
    y={i:Q(v) for i,v in pairs}
    assert verify(A,obj,y)<=0
    a,b,c=(sum(y.get(i,0)*cc[j] for i,cc in enumerate(coeff)) for j in range(3))
    q=c/18;l=(b-3*(2*n0+3)*q)/3;z=a-q*n0*n0-l*n0
    print("solver-free dual: n >=",n0,"verified variables",len(names),
          "upper polynomial",q,l,z,"excess over benchmark (n²,n,1):",q-Q(1,3),l-1,z+(Q(2),Q(4,3),Q(10,3))[residue])


def verify(A,obj,y):
    residual=Counter(obj)
    for i,z in y.items():
        row,op=A[i]
        assert op=='=' or (z<=0 if op=='>=' else z>=0)
        for x,w in row:residual[x]-=z*w
    return max(residual.values())


def recover(A,obj,raw):
    cols=defaultdict(dict)
    for i,z in raw.items():
        if abs(z)<Q(1,10**8):continue
        for x,w in A[i][0]:cols[x][i]=Q(w)
    piv={}
    candidates=[]
    for x,c in cols.items():
        gap=abs(sum(w*raw[i] for i,w in c.items())-obj[x])
        if gap<Q(1,1000):candidates.append((gap,len(c),x))
    for _,_,x in sorted(candidates):
        c=cols[x].copy();b=Q(obj[x])
        while c:
            i=min(c);w=c.pop(i)
            if i not in piv:
                piv[i]=({j:v/w for j,v in c.items()},b/w);break
            row,rb=piv[i];b-=w*rb
            for j,v in row.items():
                c[j]=c.get(j,0)-w*v
                if not c[j]:del c[j]
    y={i:z.limit_denominator(504) for i,z in raw.items() if abs(z)>=Q(1,10**8)}
    for i in sorted(piv,reverse=True):
        c,b=piv[i];y[i]=b-sum(w*y[j] for j,w in c.items())
    return y

def certificate(d=2,horizon=15,save=False,period=1,residue=2,strip=False):
    n0,names,A,coeff,obj=polynomial(d,period,residue,strip)
    def rhs(k):return [a+k*b+k*(k-1)//2*c for a,b,c in coeff]
    text="max: "+lpterms(obj)+";\n"+"".join(f"r{i}: "+lpterms(dict(row))+f" {op} {v};\n"
               for i,((row,op),v) in enumerate(zip(A,rhs(horizon))))
    res=subprocess.run(['lp_solve','-S4'],input=text,text=True,capture_output=True,check=True)
    lines=res.stdout.split('Dual values with from - till limits:')[-1].splitlines()
    raw={int(a[1:]):Q(b) for line in lines if len(line.split())==4 for a,b,_,_ in [line.split()]
         if a.startswith('r') and a[1:].isdigit()}
    assert raw
    for den in (12,36,72,144,360,2520,10000,'exact',None):
        y=recover(A,obj,raw) if den=='exact' else {i:z.limit_denominator(den) if den else z for i,z in raw.items() if z}
        for i,(c,op) in enumerate(A):
            if op=='>=':y[i]=min(0,y.get(i,0))
            if op=='<=':y[i]=max(0,y.get(i,0))
        if verify(A,obj,y)<=0:break
    else:
        # Add the exact positive residual to a normalization row having
        # positive coefficient on the offending variable.
        normal={}
        for i,(c,op) in enumerate(A):
            if op=='=' and coeff[i][0]>0 and all(w>0 for x,w in c):
                for x,w in c:normal[x]=(i,w)
        residual=Counter(obj)
        for i,z in y.items():
            for x,w in A[i][0]:residual[x]-=z*w
        for x,z in residual.items():
            if z>0:
                i,w=normal[x];y[i]=y.get(i,0)+z/w
    assert verify(A,obj,y)<=0
    # Polynomials in n (not fitted scores): sum of exact RHS polynomials
    # times one fixed dual vector.
    v0,v1,v2=(sum(y.get(i,0)*q for i,q in enumerate(rhs(j))) for j in (0,1,2))
    quad=(v2-2*v1+v0)/18
    linear=(v1-v0)/3-(2*n0+3)*quad
    constant=v0-linear*n0-quad*n0*n0
    print("period",period,"pooled correction",d,"n >=",n0,"variables",len(names),"rows",len(A),
          "nonzero multipliers",sum(bool(z) for z in y.values()),flush=True)
    print("upper polynomial (n²,n,1)",quad,linear,constant,"dual residual",verify(A,obj,y),flush=True)
    if save:
        digest=hashlib.sha256(repr((A,coeff,sorted(obj.items()))).encode()).hexdigest()
        path=filename(d,period,residue,strip)
        path.write_text(json.dumps([digest,[[i,str(z)] for i,z in sorted(y.items()) if z]],separators=(',',':'))+'\n')
    return quad,linear,constant


if __name__=='__main__':
    import sys
    period=3 if '--three' in sys.argv else 1
    residue=int(sys.argv[sys.argv.index('--residue')+1]) if '--residue' in sys.argv else 2
    strip='r28' if '--r28' in sys.argv else 'pinned' if '--pinned' in sys.argv else 'lift4' if '--lift4' in sys.argv else 'lift' if '--lift' in sys.argv else '--strip' in sys.argv
    if '--replay' in sys.argv:replay(int(sys.argv[1]),period,residue,strip)
    else:certificate(int(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 15,'--save' in sys.argv,period,residue,strip)
