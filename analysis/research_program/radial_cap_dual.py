"""Optimize a telescoping interface word price for caps of arbitrary height."""
from fractions import Fraction as Q

def graph(kind,w,history):
    root=kind!='bulk';n=w+root;histmask=(1<<history)-1
    start=(0,tuple(range(n)),0,0,0,0);states=[start];ix={start:0};arcs=[]
    for si,(old,par,flags,ht,hb,phase) in enumerate(states):
        free=((1<<w)-1)&~((old<<1)|(old>>1))
        if kind=='bottom' or kind=='top' and phase!=0:free&=~1
        m=free
        while True:
            p=[*par[:w],*range(w,2*w+root)]
            if root and par[-1]<w:p[-1]=par[-1]
            def rt(i):
                while i!=p[i]:i=p[i]
                return i
            f=[bool(flags>>j&1) for j in range(w)]+[j==w-1 or kind=='bulk' and j==0 for j in range(w)]
            if root:f.append(bool(flags>>w&1))
            bonds=[(j,w+j) for j in range(w) if (old|m)>>j&1]
            bonds += [(w+j,w+j+1) for j in range(w-1) if m>>j&3]
            if root and (kind=='bottom' or phase==0 or m&1):bonds.append((2*w,w))
            tax=0
            for a,b in bonds:
                a,b=rt(a),rt(b)
                if a==b:break
                tax+=f[a] and f[b];p[a]=b;f[b]|=f[a]
            else:
                R=list(map(rt,range(w,2*w+root)));q=tuple(R.index(a) for a in R)
                g=sum(int(f[a])<<j for j,a in enumerate(R))
                tt=(ht*2+(m&1))&histmask;bb=(hb*2+(m>>(w-1)))&histmask
                target=(m,q,g,tt if kind=='bulk' else 0,bb,(phase+1)%3)
                if target not in ix:ix[target]=len(states);states.append(target)
                gaps=int(not((old|m)>>(w-1)&1))
                if kind=='bulk':gaps+=not((old|m)&1)
                rank=2*(1+(kind=='bulk')-tax)-gaps
                low=(m&((1<<(w-1))-1)).bit_count()
                # Store three times the unpriced per-column excess.
                base=(3*low-3 if kind=='bulk' else 3*low-(w-1) if kind=='top'
                      else 3*(1+m.bit_count())-(w+1))
                key=lambda v:(phase<<history)+v
                # Bulk objective = excess + V(top)-V(bottom).
                plus=key(tt) if kind=='bulk' else key(bb) if kind=='bottom' else -1
                minus=key(bb) if kind!='bottom' else -1
                arcs.append((si,ix[target],base,rank,plus,minus))
            if m==0:break
            m=(m-1)&free
    return len(states),arcs

def solve(dt,db,history):
    import numpy as np,highspy as hs
    lp=hs.Highs();lp.setOptionValue('threads',1);lp.setOptionValue('output_flag',False)
    N=3<<history;data=[graph('bulk',4,history),graph('top',dt,history),graph('bottom',db,history)]
    total=N+3+sum(s for s,_ in data);low=np.full(total,-hs.kHighsInf);low[N]=0
    lp.addVars(total,low,np.full(total,hs.kHighsInf));lp.changeColCost(N+1,1);lp.changeColCost(N+2,1)
    offset=N+3
    for k,(num,arcs) in enumerate(data):
        for a,b,val,r,plus,minus in arcs:
            c={}
            for j,v in [(offset+b,1),(offset+a,-1),(N,-r),(plus,-1),(minus,1),(N+k if k else -1,1)]:
                if j>=0:c[j]=c.get(j,0)+v
            lp.addRow(val/3,hs.kHighsInf,len(c),list(c),list(c.values()))
        offset+=num
    lp.run();assert lp.getModelStatus()==hs.HighsModelStatus.kOptimal
    v=[Q(float(x)).limit_denominator(100000) for x in lp.getSolution().col_value]
    offset=N+3;slack=0
    for k,(num,arcs) in enumerate(data):
        for a,b,val,r,p,m in arcs:
            gap=v[offset+b]-v[offset+a]+(v[N+k] if k else 0)-Q(val,3)-r*v[N]-(v[p] if p>=0 else 0)+(v[m] if m>=0 else 0)
            slack=min(slack,gap)
        offset+=num
    print('depths',dt,db,'word',history,'states/arcs',[(n,len(a)) for n,a in data],
          'rank price',v[N],'end rates',v[N+1:N+3],'sum',sum(v[N+1:N+3]),'minimum residual',slack,flush=True)
    assert slack==0 and v[N]>=0
    return v[:N+3]
if __name__=='__main__':
    import sys
    solve(*map(int,sys.argv[1:]))
