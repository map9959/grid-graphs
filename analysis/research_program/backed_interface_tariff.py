"""All-length charge for interruptions of a six-column parallel boundary strip."""
from fractions import Fraction as Q
from functools import lru_cache
from .exterior_surface_bound import wing_opts

def graph(d):
    assert d%3==0
    w=d-1;st=[(-1,tuple(range(w+1)))];ids={st[0]:0};arcs=[]
    good=sum(1<<(d-2-x) for x in range(0,d,3))
    for i,(v,p) in enumerate(st):
        for m,q,num in wing_opts(w,v,p):
            t=m,q;j=ids.setdefault(t,len(ids))
            if j==len(st):st.append(t)
            arcs.append((i,j,num-d//3,int(m!=good)))
    return st,arcs

def potential(st,arcs,alpha):
    a,b=alpha.as_integer_ratio()
    edges=[(i,j,b*x+a*y) for i,j,x,y in arcs]
    val=[None]*len(st);val[0]=0
    for _ in st:
        change=False
        for i,j,v in edges:
            if val[i] is not None and (val[j] is None or val[j]<val[i]+v):
                val[j]=val[i]+v;change=True
        if not change:
            assert all(val[j]>=val[i]+v for i,j,v in edges)
            return Q(max(val),b)

def check(d):
    st,arcs=graph(d)
    vals=sorted({Q(i,j) for j in range(1,65) for i in range(j+1)})
    lo,hi=0,len(vals)
    while hi-lo>1:
        mid=(lo+hi)//2
        if potential(st,arcs,vals[mid]) is None:hi=mid
        else:lo=mid
    a=vals[lo];c=potential(st,arcs,a)
    print('depth',d,'states',len(st),'inequalities',len(arcs),'charge',a,'endpoint allowance',c,flush=True)
    return a,c

if __name__=='__main__':
    for d in (3,6):check(d)
