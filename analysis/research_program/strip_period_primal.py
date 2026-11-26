"""Seek a fractional obstruction on an entire residue-one tail, in Newton basis."""
from fractions import Fraction as Q
from pathlib import Path
import json,subprocess
from .repeating_patch_dual import polynomial,lpterms


def run(h=15,replay=False,lift=False):
    n0,_,A,bs,obj=polynomial(2,3,1,'lift' if lift else True)
    def at(v,j):return v[0]+j*v[1]+j*(j-1)//2*v[2]
    path=Path(__file__).with_name('strip_period_primal_r1'+('_lift' if lift else '')+'.json')
    if replay:
        f={x:tuple(map(Q,v)) for x,v in json.loads(path.read_text()).items()}
    else:
        f=recover(A,bs,obj,h,at)
    assert set(f)<=set(x for row,_ in A for x,_ in row)
    def rhs(c):return tuple(sum(w*f.get(x,(0,0,0))[i] for x,w in c) for i in range(3))
    inequalities=list(f.values())
    for (row,op),b in zip(A,bs):
        slack=tuple(u-v for u,v in zip(rhs(row),b))
        if op=='=':assert slack==(0,0,0)
        else:inequalities.append(tuple(-v for v in slack) if op=='<=' else slack)
    score=rhs(obj.items())
    assert score==(141,45,6)
    for j in range(h+1):
        if all(at(v,j)>=0 and v[2]>=0 and v[1]+j*v[2]>=0 for v in inequalities):break
    else:raise ValueError('basis does not certify the infinite tail')
    print('exact fractional primal n >=',n0+3*j,'rows',len(A),'nonzero polynomial variables',len(f),
          'Newton objective',score)
    if not replay:path.write_text(json.dumps({x:list(map(str,v)) for x,v in f.items()},separators=(',',':'))+'\n')


def recover(A,bs,obj,h,at):
    text='max: '+lpterms(obj)+';\n'+''.join(f'r{i}: '+lpterms(dict(c))+f' {op} {at(b,h)};\n'
        for i,((c,op),b) in enumerate(zip(A,bs)))
    out=subprocess.run(['lp_solve','-S2'],input=text,text=True,capture_output=True,check=True).stdout
    vals={x:Q(v) for s in out.splitlines() if len(s.split())==2 for x,v in [s.split()]
          if x.startswith('x') and x[1:].isdigit() and Q(v)>Q(1,100000)}
    piv={}
    for (row,op),b in zip(A,bs):
        if op!='=' and abs(sum(w*vals.get(x,0) for x,w in row)-at(b,h))>Q(1,100):continue
        c={x:Q(w) for x,w in row if x in vals}
        while c:
            x=min(c,key=lambda s:int(s[1:]));w=c.pop(x)
            if x not in piv:
                piv[x]=({y:v/w for y,v in c.items()},tuple(Q(k)/w for k in b));break
            pc,pb=piv[x]
            b=tuple(k-w*m for k,m in zip(b,pb))
            for y,v in pc.items():
                c[y]=c.get(y,0)-w*v
                if not c[y]:del c[y]
    f={}
    for x,(c,b) in sorted(piv.items(),key=lambda kv:-int(kv[0][1:])):
        f[x]=tuple(b[i]-sum(w*f.get(y,(0,0,0))[i] for y,w in c.items()) for i in range(3))
    return f


if __name__=='__main__':
    import sys
    run(replay='--replay' in sys.argv,lift='--lift' in sys.argv)
