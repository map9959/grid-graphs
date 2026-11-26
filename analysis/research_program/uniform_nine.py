"""Lift the 9-row dual to a repeating polynomial by repairing its leading coefficients."""
from .nine_dual import read_dual,dualfile,scale
from .seven_threshold import *
from .six_joint_replay import projected
from .six_joint_lp import polynomial
import subprocess

def instance(fifteen=False):
    ns,A,b,obj,l=model(9);_,_,_,bh,_=polynomial(5,3,1)
    bh.extend((z,0,0) for z in b[len(bh):])
    assert all(bb==a+28*d+378*e for (a,d,e),bb in zip(bh,b))
    if fifteen:
        from .fourteen_bound import core15,layout
        ns,AA,bb,obj,l,*_=core15()
        assert A==AA[:len(A)]
        for value in bb[len(A):]:
            # Refined patch normalizations are either singletons or one
            # of the three periodic column buckets of size 27..31.
            slope=int(value>1)
            assert not slope or 25<=value<=31
            bh.append((value-28*slope,slope,0))
        return ns,AA,bh,obj,layout(l,[(0,9),(6,9)])
    return ns,A,bh,obj,l

def prices(c,fifteen=False):
    if fifteen:
        cc=tuple(c.get((o,h,r,m),0) for o in (0,6) for h in range(29) for r in range(7) for m in range(512))
        from .fourteen_bound import file
        B=json.loads(file.with_name('fifteen_upper_109.json').read_text())[2]
        v,d,j=map(int,subprocess.run(['target/fifteen_price',str(B),'uniform3'],input=' '.join(map(str,cc)),text=True,capture_output=True,check=True).stdout.split())
        print('15-row uniform price, increment, insertion index',Q(v,scale),Q(d,scale),j,flush=True)
        return Q(v,scale),Q(d,scale)
    inp=' '.join(str(c.get((h,r,m),0)) for h in range(19) for r in range(7) for m in range(512))
    v,d,n=map(int,subprocess.run(['target/nine_uniform'],input=inp,text=True,capture_output=True,check=True).stdout.split())
    print('uniform path bound at 109, increment per 3, states',Q(v,scale),Q(d,scale),n,flush=True)
    return Q(v,scale),Q(d,scale)

def inputs(fifteen):
    if not fifteen:return read_dual(dualfile)
    yy,cc,_=json.loads(dualfile.with_name('fifteen_upper_109.json').read_text())
    return {int(i):Q(q) for i,q in yy.items()},{tuple(k):q for k,q in cc}
def output(fifteen):return Path(__file__).with_name('uniform_'+('fifteen' if fifteen else 'nine')+'_repair.json')
def run(fifteen=False):
    import highspy as hs
    import numpy as np
    ns,A,b,obj,l=instance(fifteen);y,c=inputs(fifteen)
    dist,step=prices(c,fifteen);cost={k:Q(v,scale) for k,v in c.items()}
    rc=projected(A,b,obj,l,y,cost)
    coeff=lambda y:[sum(q*b[i][j] for i,q in y.items()) for j in range(3)]
    by=coeff(y);unit=8*scale
    norm={}
    for i,((cs,op),bb) in enumerate(zip(A,b)):
        if op=='=' and bb[0]>0 and bb[1:]==(0,0) and all(w>0 for x,w in cs):
            for x,w in cs:norm[x]=i,w
    missing=set(ns.values())-norm.keys();xs=sorted(missing);ids={x:i for i,x in enumerate(xs)}
    h=hs.Highs();h.setOptionValue('threads',1);h.setOptionValue('output_flag',False)
    lo=lambda z:max(-1e10,float(z))
    def row(low,hi):h.addRow(low,hi,0,[],[])
    for x in xs:row(lo(rc[x]*unit),hs.kHighsInf)
    row(-hs.kHighsInf,float((57+step-by[1])*unit))
    row(float((6-by[2])*unit),float((6-by[2])*unit))
    order=[];sign=[];vectors=[];limits=[]
    for i,((cs,op),bb) in enumerate(zip(A,b)):
        t=[(ids[x],w) for x,w in cs if x in ids]
        t.extend((len(xs)+j,bb[j+1]) for j in range(2) if bb[j+1])
        if not t:continue
        for s in (-1,1):
            lim=200000000 if fifteen else 20000
            if (op=='<=' and s<0) or (op=='>=' and s>0):lim=min(lim,abs(y.get(i,0))*unit)
            if lim:
                h.addCol(1.,0,float(lim),len(t),[j for j,w in t],[float(w*s) for j,w in t])
                order.append(i);sign.append(s);vectors.append([(j,s*w) for j,w in t]);limits.append(Q(lim))
    h.run();print('uniform repair',len(xs),len(order),h.getModelStatus(),flush=True)
    if h.getModelStatus()!=hs.HighsModelStatus.kOptimal:return
    yc=y.copy();vals=[Q(v).limit_denominator(10**5) for v in h.getSolution().col_value]
    if fifteen:
        basis=h.getBasis();B=hs.HighsBasisStatus;active={i for i,st in enumerate(basis.row_status) if st!=B.kBasic}
        rhs=[max(-10**10,rc[x]*unit) for x in xs]+[(57+step-by[1])*unit,(6-by[2])*unit]
        eq={i:{} for i in active}
        for j,(st,col) in enumerate(zip(basis.col_status,vectors)):
            vals[j]=limits[j] if st==B.kUpper else Q(0)
            for i,w in col:
                if i in active:
                    if st==B.kBasic:eq[i][j]=Q(w)
                    elif vals[j]:rhs[i]-=w*vals[j]
        piv={}
        for i,cs in sorted(eq.items(),key=lambda e:len(e[1])):
            v=Q(rhs[i])
            while cs:
                j=min(cs);w=cs.pop(j)
                if j not in piv:piv[j]=({a:u/w for a,u in cs.items()},v/w);break
                row,bj=piv[j];v-=w*bj
                for a,u in row.items():
                    cs[a]=cs.get(a,0)-u*w
                    if not cs[a]:del cs[a]
            else:assert v==0
        for j,(row,v) in sorted(piv.items(),reverse=True):vals[j]=v-sum(w*vals[a] for a,w in row.items())
    for i,s,v in zip(order,sign,vals):
        if v:yc[i]=yc.get(i,0)+s*v/unit
    r=projected(A,b,obj,l,yc,cost)
    print('leading residual',max(r[x] for x in xs),'coefficients',coeff(yc)[1:],flush=True)
    assert max(r[x] for x in xs)<=0
    inc=Counter()
    for x,(i,w) in norm.items():inc[i]=max(inc[i],Q(r[x])/w)
    for i,z in inc.items():yc[i]=yc.get(i,0)+z
    assert max(projected(A,b,obj,l,yc,cost).values())<=0
    a,d,e=coeff(yc);assert e==6 and d<=57+step
    v=a+28*d+378*e-dist
    print('uniform upper at 109',v,'constant offset from 3k^2+6k',v-4104,flush=True)
    dif={i:str(yc.get(i,0)-y.get(i,0)) for i in yc if yc[i]!=y.get(i,0)}
    output(fifteen).write_text(json.dumps(dif,separators=(',',':'))+'\n')
def check(fifteen=False):
    ns,A,b,obj,l=instance(fifteen);y,c=inputs(fifteen)
    for i,q in json.loads(output(fifteen).read_text()).items():
        y[int(i)]=y.get(int(i),0)+Q(q)
    assert max(projected(A,b,obj,l,y,{k:Q(v,scale) for k,v in c.items()}).values())<=0
    first,step=prices(c,fifteen);a,d,e=[sum(q*b[i][j] for i,q in y.items()) for j in range(3)]
    assert e==6 and d-step<=57
    offset=a+28*d+378*e-first-4104
    print('all k >= 36: upper 3k^2+6k +',offset,'integer correction',offset.__floor__())
    if not fifteen:assert offset.__floor__()==-9
if __name__=='__main__':
    args=__import__('sys').argv
    (run if '--build' in args else check)('--fifteen' in args)
