"""Period-nine rail backgrounds and exact cyclic boundary-arm costs."""
from collections import Counter
from functools import lru_cache
from itertools import product


def backgrounds(p=9):
    n=2*p
    for phase in range(3):
        for signs in product((-1,1),repeat=2*(p//3)):
            d={}
            def put(i,j,x,y):
                q=(i+x)%n,(j+y)%n
                assert (i,j) not in d and q not in d
                d[i,j],d[q]=(x,y),(-x,-y)
            for i,j in product(range(p),repeat=2):
                band,z=divmod((i-phase)%p,3)
                put(2*i,2*j,*((0,signs[band]) if not z else (2*z-3,0)))
                put(2*i+1,2*j+1,*((0,signs[p//3+band]) if z==1 else (1-z,0)))
            yield d
            yield {(j,i):(y,x) for (i,j),(x,y) in d.items()}


def profile(d,h,side,last,n):
    # Local coordinates (normal inward, tangent increasing). All physical
    # sides have even normal coordinate. Only the first background collar matters.
    def direction(i,j):
        r=i if side in ('top','left') else last-i
        c=j
        if side in ('left','right'):r,c=c,r
        x,y=d[r%n,c%n]
        if side in ('left','right'):x,y=y,x
        return (-x if side in ('bottom','right') else x),y
    m=h+(h%2)
    data=[]
    for j in range(n):
        port=direction(h,j)==(-1,0)
        # On odd doubled row a primal edge midpoint denotes a normal
        # edge: it must point normally; on even row a tangent edge.
        fixed=sum(1<<i for i in range(h,m+2) if (i+j)%2 and
                  (direction(i,j)[1]==0)==bool(i%2))
        data.append((port,fixed))
    return tuple(min(data[t:]+data[:t] for t in range(0,n,2)))


@lru_cache(None)
def words(h,port,fix,parity):
    out=[]
    def rec(i,l,r,mask):
        if i>=h:
            out.append((l,r,mask|fix));return
        tangent=(i+parity)%2 and i%2==0
        if i==h-1 and port:
            rec(i+1,l,r,mask|((1<<i) if (i+parity)%2 and i%2 else 0));return
        bit=1<<i
        rec(i+1,l|bit,r,mask|(bit if tangent else 0))
        rec(i+1,l,r|bit,mask|(bit if tangent else 0))
        if i+1<h and not (i+1==h-1 and port):
            normal=i if i%2 else i+1
            rec(i+2,l,r,mask|((1<<normal) if parity==0 else 0))
    rec(0,0,0,0)
    return out


@lru_cache(None)
def arm(h,prof):
    # Pair odd/even columns. At a tangent cut remember rightward domino
    # ports and the primal labels in the preceding odd midpoint column.
    # A pair closes all stars centered on its even column.
    n=len(prof);m=h+h%2
    graphs=[]
    for j in range(0,n,2):
        before=words(h,*prof[j-1],1)
        even=words(h,*prof[j],0)
        after=words(h,*prof[j+1],1)
        edges={}
        for _,start,prev in before:
            src=start,prev
            if src in edges:continue
            ds=edges[src]={}
            for l,r,mid in even:
                if start!=l:continue
                for l2,r2,nxt in after:
                    if r!=l2:continue
                    degs=[((prev>>i)&1)+((nxt>>i)&1)+((mid>>(i+1))&1)+
                          (((mid>>(i-1))&1) if i else 0) for i in range(0,m+1,2)]
                    loss=sum(0 if v==4-int(i==0) else v-1+int(i==0)
                             for i,v in enumerate(degs))
                    assert min(degs)>=1 and loss>=0
                    dest=r2,nxt
                    ds[dest]=min(ds.get(dest,1000),loss)
        graphs.append(edges)
    # A physical circumference requires a closed walk.
    best=1000
    for src in graphs[0]:
        curr={src:0}
        for graph in graphs:
            new={}
            for s,cost in curr.items():
                for q,w in graph.get(s,{}).items():
                    v=cost+w
                    if v<best and v<new.get(q,1000):new[q]=v
            curr=new
        best=min(best,curr.get(src,1000))
    return best


def budgets(p,residue,a=4,b=4):
    last=8+6*residue
    out=[]
    for idx,d in enumerate(backgrounds(p)):
        costs=[]
        for side,h in [('top',a),('right',9-b),('bottom',9-a),('left',b)]:
            prof=profile(d,h,side,last,2*p)
            if sum((-1)**j for j,(port,_) in enumerate(prof) if port):
                costs.append(1000)
            else:costs.append(arm(h,prof))
        out.append((idx,d,costs))
    return out


def pairs(p,residue):
    rows=budgets(p,residue)
    return rows,[(i,j,p-sum(l[:2])-sum(h[2:]))
                 for i,_,l in rows for j,_,h in rows if sum(l[:2])+sum(h[2:])<=p]


def state(d,rev=False):
    def get(i,j):
        x,y=d[(-i if rev else i)%18,(-j if rev else j)%18]
        return (-x,-y) if rev else (x,y)
    def cross(di,step):
        return sum(1<<c for c in range(18) if get(c+di,c)==step)
    v,h=cross(-1,(1,0)),cross(-1,(0,-1))
    m=(v|cross(-2,(1,0)))^0x2aaaa
    return v|h>>1|(h&1)<<17,m


def census():
    import subprocess
    from pathlib import Path
    cases=[];queries=set()
    for r in range(3):
        rows,c=pairs(9,r)
        cases.append(c);queries.update(c)
        print("k mod 3",(r+1)%3,"interface budgets:",dict(Counter(v for _,_,v in c)),flush=True)
    queries.update((i,i,0) for i in range(len(rows))
                   if state(rows[i][1])[0].bit_count()==9)
    positive=[(i,112,2) for i in (50,56,84,88,98,100)]
    queries.update(positive)
    lines=[" ".join(map(str,[*state(rows[i][1]),*state(rows[j][1],True),v,i,j]))
           for i,j,v in sorted(queries)]
    binary=Path(__file__).resolve().parents[2]/"target/release/diagonal_nine"
    out=subprocess.run([binary],input="\n".join(lines),text=True,capture_output=True,check=True)
    results={}
    for q,line in zip(sorted(queries),out.stdout.splitlines(),strict=True):
        i,j,s=map(int,line.split())
        assert (i,j)==q[:2]
        results[q]=s
    controls=[v for (i,j,b),v in results.items() if i==j and b==0]
    assert set(controls)=={0}
    assert all(results[q]==2 for q in positive)
    print("identical background controls:",len(controls),flush=True)
    print("nonidentical positive control transitions of cost 2:",len(positive),flush=True)
    for r,c in enumerate(cases):
        print("k mod 3",(r+1)%3,"survivors:",[q for q in c if results[q]<=q[2]],flush=True)


if __name__=="__main__":
    census()
