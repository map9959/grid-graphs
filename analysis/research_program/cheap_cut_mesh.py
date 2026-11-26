"""Cross two families of unrestricted cheap lines; retain entire monochrome spans."""
from itertools import product
from .comb_cap_transfer import construct

def bit(t,x):
    return int(t==3 or (t<3 and x%3==t))

def crossing():
    cases=0
    for row,col,x,y in product(range(5),range(5),range(3),range(3)):
        l,m,r=(bit(row,i) for i in (x-1,x,x+1))
        u,v,d=(bit(col,i) for i in (y-1,y,y+1))
        if m!=v or not any((l,m,r,u,d)) or m and not (l or u):continue
        if (l or r) and (u or d):continue # diagonal marked pair
        assert (row<3)!=(col<3)
        cases+=1
    print('clean crossing cases',cases)

def bills(rows,limit=2):
    n=len(rows);result={}
    for i in range(2,n,3):
        events=[]
        for y in (i-1,i,i+1):
            for x in range(n):
                if rows[y][x]=='#' and rows[y-1][x]=='.' and (not x or rows[y][x-1]=='.'):
                    events.append(x)
        for x in range(n):
            if all(rows[y][z]=='.' for y,z in ((i,x),(i-1,x),(i+1,x),(i,x-1),(i,x+1)) if 0<=z<n):
                events.append(x)
        if limit is None or len(events)<=limit:result[i]=events
    return result

def mesh(rows,L=24):
    tr=list(zip(*rows));er,ec=bills(rows),bills(tr)
    t=min(len(er),len(ec))//L
    if not t:return
    def groups(e):return [sorted(e)[i*t:(i+1)*t] for i in range(L)]
    def keep(lines,e,opposite,charge):
        lo,hi=opposite[0]-1,opposite[-1]+1
        def kind(i):
            if charge and any(lo<=x<=hi for x in e[i]):return
            for q in range(5):
                if all(bit(q,x)==(lines[i][x]=='#') for x in range(lo,hi+1)):return q
        return kind
    best=(0,0);frame=None
    for rr,cc in product(groups(er),groups(ec)):
        a=keep(rows,er,cc,True);b=keep(tr,ec,rr,True)
        A={i:v for i in rr if (v:=a(i)) is not None}
        B={j:v for j in cc if (v:=b(j)) is not None}
        if not A or not B:continue
        assert all((u<3)!=(v<3) for u in A.values() for v in B.values())
        score=min(len(A),len(B)),len(A)+len(B)
        if score>best:
            best=score;frame=(rows,A,B) if min(A.values())<3 else (tr,B,A)
    assert best[0]>=(t+1)//2
    print('side',len(rows),'cheap lines',len(er),len(ec),'group size',t,'mesh min dimension',best[0])
    lines,A,B=frame
    ys=sorted(A);halves=(ys[:(len(ys)+1)//2],ys[len(ys)//2:])
    options=[]
    for half in halves:
        rails=set()
        for j in B:
            for x in (j,j+1,j-1):
                if all(lines[y][x]=='#' for y in range(half[0],half[-1]+1)):
                    rails.add(x);break
        options.append((len(rails),sorted(rails),half))
    count,pins,ys=max(options)
    assert 2*count>=len(B)
    if len(ys)>=2 and count>=2:
        x,z=pins[0],pins[-1];h=ys[-1]-ys[0]+1
        assert (z-x)%3==0 and all((lines[y][j]=='#')==((j-x)%3==0)
                                    for j in range(x,z+1) for y in ys)
        m=sum(lines[y][j]=='#' for y in range(ys[0],ys[-1]+1) for j in range(x,z+1))
        assert m<=h*(1+(z-x)//3)
        print('framed rectangle',h,'by',z-x+1,'pins',count,'marks',m,'tariff',h*(1+(z-x)//3))

if __name__=='__main__':
    crossing()
    for n in (193,403):mesh(construct(n,4))
