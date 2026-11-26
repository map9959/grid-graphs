"""Exact replay of a joined strip dual on a diagonal-sector chart."""
from .repeating_patch_dual import Q,Path,json,Counter,verify
from .patch_square import relaxation,SYM,trans
from .seven_threshold import move,masks
from .chart_counts import count
from functools import lru_cache
from math import lcm
import sys

def check(n,H,d,w,build=False):
    base=43+(n-43)%6;ns,rows,obj=relaxation(base,d+4,pooled=d,period=3,diagonal=w)
    inv={x:k for k,x in ns.items()};S=n-2
    def pos(i,j):
        h=d+3;ax=lambda z:z if z<h else 2*h+3+z-S if z>=S-h else h+(z-h)%3
        cut=lambda a:max(-w-5,min(w+5,a))
        return ax(i),ax(j),cut(i-j),cut(i+j+1-S)
    pp={}
    for r in range(H-2):
        for j in range(S):
            z=tuple(pos(*trans(r,j,S,g)) for g in range(8))
            assert pp.setdefault((r,z[0]),z)==z
    source=int(next((x.split('=')[1] for x in sys.argv if x.startswith('--source=')),n))
    assert (n-source)%6==0
    path=Path(__file__).with_name(f'diagonal_strip{H}_{source}.json')
    if build:
        raw,cc=json.loads(Path('target',path.name).read_text())
        exact='--rounded' not in sys.argv
        cv=lambda z:Q(z).limit_denominator(100000) if exact else Q(round(z*10**10),10**10)
        y={i:cv(z) for i,z in enumerate(raw) if z}
        cost={(r,tuple(p),m):cv(z) for (r,p,m),z in cc if z}
    else:
        yy,cc=json.loads(path.read_text());y={int(i):Q(z) for i,z in yy.items()};cost={(r,tuple(p),m):Q(z) for (r,p,m),z in cc}
    ob=Counter(obj)
    for (r,p,m),q in cost.items():ob[ns['p',min(zip(pp[r,p],SYM[m]))]]+=q
    A=[];coef=[];norm={}
    for i,(cs,op,b) in enumerate(rows):
        A.append((cs,op))
        if b and op=='=':
            kind,z=inv[cs[0][0]];p=int(kind=='p')
            coef.append(count(n-2*p,d+4-p,w+5,z[0]))
            for x,v in cs:norm[x]=i,v
        else:coef.append((b,0,0))
    if build:
        resid=ob.copy()
        for i,z in list(y.items()):
            cs,op=A[i]
            if op!='=':y[i]=z=min(z,0) if op=='>=' else max(z,0)
            for x,v in cs:resid[x]-=v*z
        inc=Counter()
        for x,z in resid.items():
            if z>0:
                i,v=norm[x];inc[i]=max(inc[i],z/v)
        for i,z in inc.items():y[i]=y.get(i,0)+z
    assert verify(A,ob,y)<=0
    hx=lcm(*(z.denominator for z in cost.values()));ic={k:int(z*hx) for k,z in cost.items()}
    start=(0,0,tuple(range(H)));dp={start:0}
    @lru_cache(None)
    def opts(s):
        a,b,p=s
        return [( (b,c,q),masks(a,b,c,H)) for c in range(1<<H) if (q:=move(b,p,c)) is not None]
    @lru_cache(None)
    def layer(st,loc):
        return [(s,z,sum(ic.get((r,loc[r],m),0) for r,m in enumerate(ms)) if loc else 0) for s in st for z,ms in opts(s)]
    def advance(dp,j):
        loc=tuple(pos(r,j-2) for r in range(H-2)) if j>=2 else ()
        nd={}
        for s,z,v in layer(tuple(sorted(dp)),loc):
            a=dp[s]+v
            if z not in nd or a<nd[z]:nd[z]=a
        return nd
    middle=n//2
    for j in range(n):
        if j==middle:prev=dp
        if j==middle+6:
            assert prev.keys()==dp.keys()
            step=Q(min(dp[s]-v for s,v in prev.items()),hx)
        dp=advance(dp,j)
    val=Q(min(dp.values()),hx)
    a,b,e=[sum(z*coef[i][j] for i,z in y.items()) for j in range(3)]
    print('exact side',n,'strip',H,'upper',float(a-val),'integer upper',(a-val).__floor__(),
          'width +6 Newton',float(b-step),float(e),'path increment',float(step),flush=True)
    if build:path.write_text(json.dumps([{i:str(z) for i,z in y.items() if z},[[k,str(z)] for k,z in cost.items() if z]],separators=(',',':'))+'\n')
if __name__=='__main__':check(*map(int,sys.argv[1:5]),'--build' in sys.argv)
