"""Horizontal interface flux with physical forced-edge arrows and word phases.

Each column fixes the vertical arrows. On a horizontal edge, spend the
old vertex's outgoing edge whenever available; this leaves a superset
of the possible future states at the new vertex.
"""
from itertools import product
from functools import lru_cache
from fractions import Fraction as Q

def exact_point(lp,rows):
    import highspy as hs
    basis=lp.getBasis();raw=lp.getSolution().col_value
    x=[None if s==hs.HighsBasisStatus.kBasic else Q(round(v)) for s,v in zip(basis.col_status,raw)]
    piv={}
    for (row,rhs),status in zip(rows,basis.row_status):
        if status==hs.HighsBasisStatus.kBasic:continue
        rhs=Q(rhs);r={}
        for k,c in row.items():
            if x[k] is None:
                if c:r[k]=Q(c)
            else:rhs-=c*x[k]
        while r:
            j=min(r);coef=r.pop(j)
            if j not in piv:piv[j]=({k:c/coef for k,c in r.items()},rhs/coef);break
            p,b=piv[j];rhs-=coef*b
            for k,c in p.items():
                r[k]=r.get(k,0)-coef*c
                if not r[k]:del r[k]
        else:assert rhs==0
    for j in sorted(piv,reverse=True):
        p,b=piv[j];x[j]=b-sum(c*x[k] for k,c in p.items())
    assert all(z is not None for z in x)
    assert all(sum(c*x[k] for k,c in row.items())>=b for row,b in rows)
    return x

def graph(kind,h,pairs):
    w=h+2;allbits=(1<<w)-1;inside=(1<<h)-1
    @lru_cache(None)
    def choices(m):
        forced=[i for i in range(w-1) if m>>i&3]
        res=set()
        for ways in product((0,1),repeat=len(forced)):
            # bit 0 direction: smaller row sends down. 1: larger sends up.
            out=dict(zip(forced,ways))
            if kind=='top' and out.get(0,1)!=1:continue
            if kind=='bottom' and out.get(h,0)!=0:continue
            send=[i+way for i,way in zip(forced,ways)]
            if len(set(send))<len(send):continue
            code=lambda i:0 if i not in out else 2*((m>>i&3)-1)+1+out[i]
            res.add((sum(1<<i for i in send),code(0),code(h)))
        return list(res)
    @lru_cache(None)
    def step(old,part,m):
        p=list(part)+list(range(w,2*w))
        def rt(i):
            while p[i]!=i:i=p[i]
            return i
        for j in range(w):
            for k,on in ((j,old>=0 and (old|m)>>j&1),(w+j-1,j and m>>(j-1)&3)):
                if on:
                    a,b=rt(k),rt(w+j)
                    if a==b:return None
                    p[a]=b
        R=list(map(rt,range(w,2*w)));return tuple(R.index(r) for r in R)
    hist=7**pairs;N=7*hist
    init=(-1,tuple(range(w)),0,0,0,0,0);S=[init];ix={init:0};arcs=[]
    for i,(old,part,used,lt,lb,ph,prevbot) in enumerate(S):
        free=allbits if old<0 else allbits&~(old<<1|old>>1)
        m=free
        while True:
            if ((kind!='top' or (m&1)==int(ph==0) and not(ph!=0 and m&2))
                and (kind!='bottom' or m>>(w-1)==0 and not(m>>h&1 and prevbot))):
                mask=step(old,part,m)
                if mask is not None:
                    covered=0 if old<0 else (old|m)&used
                    for f,t,b in choices(m):
                        if covered&f:continue
                        state=(m,mask,f|covered,(lt*7+t)%hist,(lb*7+b)%hist,(ph+1)%3,
                               ((prevbot*2+(m>>h&1))&3) if kind=='bottom' else 0)
                        if state not in ix:ix[state]=len(S);S.append(state)
                        p=(ph*N+(lt*7 if pairs else 0)+t) if kind!='top' else -1
                        z=(ph*N+(lb*7 if pairs else 0)+b) if kind!='bottom' else -1
                        arcs.append((i,ix[state],3*((m>>1)&inside).bit_count()-h,p,z))
            if not m:break
            m=(m-1)&free
    return len(S),arcs

def solve(h,dt,db,pairs):
    import numpy as np,highspy as hs
    N=3*7**(pairs+1);data=[]
    for typ,k in [('bulk',h),('top',dt),('bottom',db)]:
        data.append(graph(typ,k,pairs))
        print(typ,'states/arcs',data[-1][0],len(data[-1][1]),flush=True)
    # Eliminate the state potentials by separating positive cycles. An
    # added row is an actual cycle, necessary for any consistent flux.
    lp=hs.Highs();lp.setOptionValue('threads',1);lp.setOptionValue('output_flag',False)
    lp.addVars(N+2,np.full(N+2,-100.),np.full(N+2,100.))
    lp.changeColCost(N,1);lp.changeColCost(N+1,1)
    import os,subprocess
    # Reuse the finite transition graphs over multiple pricing calls.
    proc=subprocess.Popen(['target/flux_cycle'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
    proc.stdin.write('3\n')
    for ns,arcs in data:
        proc.stdin.write(f'{ns} {len(arcs)}\n');proc.stdin.writelines(' '.join(map(str,a))+'\n' for a in arcs)
    proc.stdin.flush()
    seen=set();rows=[]
    threshold=Q(os.environ['CAP_TARGET']) if 'CAP_TARGET' in os.environ else None
    try:
        for it in range(1000):
            lp.run();assert lp.getModelStatus()==hs.HighsModelStatus.kOptimal
            if threshold is not None and lp.getObjectiveValue()/3+1/3>float(threshold)+1e-8:
                # A dual using just valid cycle rows gives a lower bound on
                # every possible interface price, even outside the search box.
                y=[Q(float(z)).limit_denominator(1000000) for z in lp.getSolution().row_dual]
                acc=[Q(0)]*(N+2);obj=0
                for v,(r,b) in zip(y,rows):
                    if not v:continue
                    assert v>0
                    obj+=v*b
                    for k,t in r.items():acc[k]+=v*t
                if acc==[0]*N+[1,1] and obj/3+Q(1,3)>threshold:
                    print('exact obstruction in this flux family:',obj/3+Q(1,3),'positive cycle constraints',sum(v>0 for v in y),flush=True)
                    return None
            vals=exact_point(lp,rows)
            from math import lcm
            scale=lcm(*(z.denominator for z in vals))
            tol=0
            if scale>=10**25:
                # Discovery only: each arc has at most three rounded
                # coefficients, so a cycle above this tolerance is a
                # genuine violation. Never certify with an approximate pass.
                scale=10**16;tol=2
            proc.stdin.write(f'{N} {scale} '+' '.join(str(round(z*scale)) for z in vals)+f' {tol}\n');proc.stdin.flush()
            new=0
            for j,(_,arcs) in enumerate(data):
                line=list(map(int,proc.stdout.readline().split()));assert line[0]==len(line)-1
                if not line[0]:continue
                row={};rhs=0
                for k in line[1:]:
                    _,_,v,p,m=arcs[k];rhs+=v
                    if p>=0:row[p]=row.get(p,0)-1
                    if m>=0:row[m]=row.get(m,0)+1
                if j:row[N+j-1]=line[0]
                key=tuple(sorted(row.items())),rhs
                if key in seen:raise ArithmeticError(f'inexact price separation at iteration {it}; numerical cap rate {lp.getObjectiveValue()/3+1/3}')
                seen.add(key);rows.append((row,rhs));new+=1
                lp.addRow(rhs,hs.kHighsInf,len(row),list(row),list(row.values()))
            if not new:
                if tol:raise ArithmeticError('large-denominator candidate needs exact potential replay')
                print('exact flux; end rates in thirds',vals[-2:],'cap bonus per column',sum(vals[-2:])/3+Q(1,3),'cuts',it,flush=True)
                return vals
    finally:proc.stdin.close();proc.wait()
    raise AssertionError('cut limit')
if __name__=='__main__':
    import sys
    solve(*map(int,sys.argv[1:]))
