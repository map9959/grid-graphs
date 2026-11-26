"""Joint elbow price on the editable four layers against BOTH port forests."""
from collections import Counter
from .sparse_component_exchange import Forest
from .core_boundary_envelope import accounting,prices
from .arbitrary_collar_transfer import engine,marks
from .wired_crop_exchange import ring

def data(rows,h=6,w=4):
    n=len(rows);m=n-2*h;p=m-2*w
    D=lambda i,j:min(i,j,n-1-i,n-1-j)
    M={(i,j) for i,s in enumerate(rows) for j,c in enumerate(s) if c=='#'}
    F=Forest(n);outer=inner=0
    for v in M:
        i,j=v;d=D(i,j)
        if h<=d<h+w:continue
        outer+=d<h;inner+=d>=h+w
        for q in ((i-1,j),(i+1,j),(i,j+1),(i,j-1)):
            if min(q)<0 or max(q)>=n or h<=D(*q)<h+w or q in M and q<v:continue
            assert F.join(v,q)
    sites={};o=Counter();k=Counter()
    for d in range(h,h+w):
        for y,x in ring(n-2*d):
            i,j=y+d,x+d;ports=[]
            for q in ((i-1,j),(i+1,j),(i,j+1),(i,j-1)):
                dep=D(*q)
                if h<=dep<h+w:continue
                g=F.root(q);(o if dep<h else k)[g]+=1
                ports.append((g,q in M))
            blocked=any((a,b) in M and not h<=D(a,b)<h+w
                        for a in (i-1,i+1) for b in (j-1,j+1))
            sites[y+d-h,x+d-h]=ports,blocked
    c=[s[h+w:-h-w] for s in rows[h+w:-h-w]]
    return sites,o,k,outer,inner,c

def certify(rows,closed=False):
    sites,o,k,R,I,c=data(rows);n=len(rows);m=n-12;p=n-20
    z=marks(rows)-R-I
    ledger,(D,cc,r,_,_)=accounting(c)
    U=min(ledger,*prices(c)[1])
    # Cached by choice of roots, not by any assumed core profile.
    caps={}
    def price(S,scale,fee):
        key=frozenset(S),scale,fee
        if key in caps:return caps[key]
        tab=[['A']*m for _ in range(m)]
        for (i,j),(ports,blocked) in sites.items():
            must=sum(g in S and b for g,b in ports);opt=sum(g in S and not b for g,b in ports)
            tab[i][j]=chr(65+3*must+opt+9*blocked)
        a=sum(engine(('closed-price' if closed else 'bridge-price',4,0,scale,fee),[''.join(row) for row in tab])[0])
        assert scale*z<=a+fee*max(0,len(S)-1)
        caps[key]=a;return a
    best=unseen=1000000;bestcase=None
    # For small selected label sets, high fees prohibit redundant
    # returns. For all inner labels, price one per three marks.
    for cut in (1,2,3,6,12,40,100000):
        O={g for g,t in o.items() if t>=cut}
        K={g for g,t in k.items() if t>=cut};S=O|K
        for scale,fee in ((1,0),(3,1),(1,1),(1,2)):
            a=price(S,scale,fee)
            cz=(a+fee*max(0,len(S)-1))//scale
            if R+cz+U<best:best=R+cz+U;bestcase=cut,scale,fee,cz
        # Never read the inner labels when constructing this weighted
        # input: every core-facing port is charged. Eliminate the unknown
        # component count with the core's exact ledger.
        a=price(O|set(k),3,1);budget=3*R+a+len(O)-1+p*p+D
        unseen=min(unseen,(budget*p+16*n-170)//(3*p+1))
        if (budget-r)//3<best:best=(budget-r)//3;bestcase=cut,3,1,'ledger'
    best=min(best,unseen);assert best>=marks(rows) and unseen>=marks(rows)
    print('closed' if closed else 'relaxed','side',n,'six/band/core',R,z,I,'port classes',len(o),len(k),
          'joint upper without inner partition',unseen,'with partition',best,bestcase,flush=True)
    return unseen,best

if __name__=='__main__':
    import sys
    from .dense_joint_collar import punctures
    from .comb_cap_transfer import construct
    from .crop_end_coupling import locked_fringe
    from .extend_forest_28 import verify
    for name,r in [('double returns',punctures(103,True)),('comb',construct(103,4)),('locked',locked_fringe(103))]:
        print(name,flush=True);certify(verify(r,True),'--closed' in sys.argv)
