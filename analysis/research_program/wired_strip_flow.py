"""Link a single rooted boundary strip to the D4 sector chart by patch marginals."""
from collections import Counter,defaultdict
from functools import lru_cache
import sys
from .wired_crop_sector import model,solve,count
from .patch_square import trans,SYM,MASKS

@lru_cache(None)
def advance(h,state,v,side,top=True,bottom=False):
    a,b,part=state
    if b>=0 and b&(v<<1|v>>1):return
    # h old sites, the common root, then h new sites
    q=list(part)+list(range(h+1,2*h+1))
    def rt(x):
        while x!=q[x]:x=q[x]
        return x
    def join(x,y):
        x,y=rt(x),rt(y);q[x]=y;return x!=y
    for i in range(h):
        j=h+1+i
        if b>=0 and (b|v)>>i&1 and not join(i,j):return
        if i and v>>(i-1)&3 and not join(j-1,j):return
        if (top and not i or bottom and i==h-1 or side) and v>>i&1 and not join(j,h):return
    new=[rt(h+1+i) for i in range(h)]+[rt(h)]
    return b,v,tuple(new.index(r) for r in new)

def add_flow(ns,A,base,d,w,h):
    flow=defaultdict(Counter);patch=defaultdict(Counter)
    pooled='--pooled' in sys.argv
    depth=4 if pooled else max(d+6,w+h+7)
    assert base>=2*depth+9
    def ax(j):return j if j<depth else j-base+2*depth+3 if j>=base-depth else depth+(j-depth)%3
    def key(i,j):
        S=base-2;l=d+3;cl=lambda z:max(-w-5,min(w+5,z))
        u=lambda x:x if x<l else 2*l+3+x-S if x>=S-l else l+(x-l)%3
        return u(i),u(j),cl(i-j),cl(i+j+1-S)
    initial=(-1,-1,tuple(range(h+1)));states={initial};seen=set();positions=set()
    for j in range(base):
        jj=(ax(j),ax(j+1));side=j in (0,base-1);nxt=set()
        for s in states:
            for v in range(1<<h):
                z=advance(h,s,v,side)
                if z is None:continue
                nxt.add(z);edge=jj,s,v
                if edge in seen:continue
                seen.add(edge);x='x'+str(len(ns));ns['strip',edge]=x
                flow[jj[0],s][x]+=1
                if j<base-1:flow[jj[1],z][x]-=1
                if j<2:continue
                for i in range(h-2):
                    mask=sum(((col>>(i+u)&1)<<(3*u+k)) for u in range(3) for k,col in enumerate((s[0],s[1],v)))
                    patch[i,jj if pooled else key(i,j-2),mask][x]+=1
        states=nxt
        if j<2:continue
        for i in range(h-2):
            pts=[key(*trans(i,j-2,base-2,g)) for g in range(8)]
            if (i,pts[0]) in positions:continue
            positions.add((i,pts[0]))
            for m in MASKS:
                x=ns.get(('p',min(zip(pts,SYM[m]))))
                if x:patch[i,jj if pooled else pts[0],m][x]-=1
    init=(ax(0),initial)
    rows=[(list(c.items()),'=') for c in patch.values()]
    rows.extend((list(c.items()),'=') for k,c in flow.items() if k!=init)
    rows.append((list(flow[init].items()),'='))
    A.extend(rows)
    return len(rows)

def test(base,d,w,h,sizes):
    ns,A,keys,obj=model(base,d,w)
    m=add_flow(ns,A,base,d,w,h);print('height',h,len(ns),'columns',m,'new rows',flush=True)
    for n in sizes:
        assert (n-base)%6==0 and n>=base
        rhs=[count(n-2*(k[0]=='p'),d+4-(k[0]=='p'),w+5,k[1][0])[0] if k else 0 for k in keys]
        v,_,_=solve(A,rhs+[0]*(m-1)+[1],obj,ns,interior=True)
        print(n,'deficit',n*n/3-v,flush=True)
if __name__=='__main__':
    import sys
    base,d,w,h,*sizes=map(int,[s for s in sys.argv[1:] if not s.startswith('--')]);test(base,d,w,h,sizes)
