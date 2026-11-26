"""Joint price for a dense ten-layer collar and the components it consumes."""
from collections import Counter
from .arbitrary_collar_transfer import engine,marks,construct
from .core_boundary_envelope import accounting,prices,projected_ledger,outside_labels
from .dense_joint_collar import punctures,upper
from .sparse_component_exchange import graph
from .extend_forest_28 import verify
from .wired_crop_exchange import ring

def price(rows,fixed=6):
    n=len(rows);m=n-20;c=[s[10:-10] for s in rows[10:-10]]
    I=marks(c);T=marks(rows)-I
    base,info=accounting(c);D,classes,r,_,_=info
    p=sum(engine(('port-price',10,fixed,3,1),rows)[0])
    # Contracting the core into one root can create at most c-1 new
    # cycles. That c is already a debit in the core ledger.
    joint=min((m*m+D-r-1+p)//3,((m*m+D-1+p)*m+16*n-170)//(3*m+1))
    # Preserve one actual core component in each exact elbow sweep. All
    # other contacts are relaxed. Never identify unrelated core vertices.
    F=graph(c,set());labs={v:F.root(v) for v in ring(m)}
    masks=[]
    for side in range(4):
        def rot(i,j):
            for _ in range(side):i,j=j,m-1-i
            return i,j
        sites=[rot(0,j) for j in range(n//2-10)]+[rot(i,0) for i in range(n-n//2-10)]
        root=Counter(labs[v] for v in sites).most_common(1)[0][0]
        mask=[['.']*n for _ in range(n)]
        for i,j in sites:
            if labs[i,j]==root:mask[10+i][10+j]='#'
        masks+=[''.join(s) for s in mask]
    A=sum(engine(('port-cap',10,fixed),list(rows)+masks)[0])
    unroot=sum(engine(('outer',10,fixed),rows)[0])
    assert T<=A<=unroot and 3*T<=p+classes-1
    u=min(base,*prices(c)[1])
    actual=min(T+u,joint)
    conditional=min(min(A,16*n-170)+u,joint)
    assert actual>=marks(rows)
    # The second joint inequality needs no interior partition or marks
    # beyond the first core word.
    coarse=((m*m+D-1+p)*m+16*n-170)//(3*m+1)
    print('side',n,'fixed depth',fixed,'ten count/cap/port cap',T,unroot,A,'priced',p,
          'joint no-core / conditional / measured upper',coarse,conditional,actual)
    return coarse,conditional,actual

def diffuse(rows):
    n=len(rows);m=n-20;bad=0;O=0;r=rows;ends=[];seen=[]
    c=[s[10:-10] for s in rows[10:-10]];F=graph(c,set())
    for side in range(4):
        z={}
        for x in range(10,n-10):
            bad+=any((r[y][x]=='#')!=(y%3==0) for y in range(10))
            if r[9][x]==r[10][x]=='#':
                p=(0,x-10)
                for _ in range(side):p=(m-1-p[1],p[0])
                z[x]=F.root(p);O+=1
        ends.append(z);r=list(map(''.join,zip(*r[::-1])))
    for i in range(2):
        last=-10;count=0
        for j,v in sorted(ends[i].items()):
            if j-last>=3 and ends[i+2].get(n-1-j)==v:last=j;count+=1
        seen.append(count)
    # A double-counted straight carrier needs collinear opposite ports
    # in the same actual class; vertical and horizontal spans cannot cross.
    P=max(seen);B=(bad-8+2)//3
    rmin=accounting(c)[1][2]
    value=(n*n+4*n-1-B-max(-P,rmin-O))//3
    assert value>=marks(rows)
    return bad,P,value

if __name__=='__main__':
    from .crop_end_coupling import locked_fringe
    for name,rows in [('comb',construct(103,4)),('locked',locked_fringe(103)),('double',punctures(103,True))]:
        rows=verify(rows,True)
        print(name,'nonpitch, through allowance, broad upper',diffuse(rows))
        price(rows)
