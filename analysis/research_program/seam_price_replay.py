"""Extract and physically check a horizontal strip independently of price summation."""
from .cross_seam_bound import rowchart,ht,BASE,horizontal
from .ordered_seam_price import sym

def replay(axis,k,q,i,j,A,B,top,bot):
    r=rowchart(j,k)
    def allow(x,w):
        return ((j or w[0]==top[x]) and (j!=k-2 or w[1]==bot[x])
                and (x!=i or w==(A[0],B[0])) and (x!=i+1 or w==(A[1],B[1])))
    def cost(w):return (1+(j==0))*(3-w[0].bit_count())+(1+(j==k-2))*(3-w[1].bit_count())
    ts=[ht(axis,rowchart(x,k),r,max(-4,min(5,q-x))) for x in range(k-1)]
    st={}
    for w in ts[0]:
        z=horizontal(BASE,w,True,r)
        if z is not None and allow(0,w):st[w,z]=cost(w),None
    hist=[st]
    for x,t in enumerate(ts,1):
        nd={};end=x==k-1
        for key,(v,_) in st.items():
            w,z=key
            for y in t.get(w,()):
                if not allow(x,y):continue
                g=horizontal(z,y,end,r)
                if g is None or end and 2 in g[2]:continue
                d=v+cost(y)
                if (y,g) not in nd or d<nd[y,g][0]:nd[y,g]=d,key
        st=nd;hist.append(st)
    key=min(st,key=lambda b:st[b][0]);value=st[key][0];path=[]
    for layer in reversed(hist):path.append(key[0]);key=layer[key][1]
    path.reverse()
    # Forced grid edges on the actual sites of this strip, no frontier labels.
    N=3*k;X={(3*x+t//3,3*h+t%3) for x,p in enumerate(path) for h,m in enumerate(p)
             for t in range(9) if m>>t&1}
    seen=set()
    for u in X:
        if u in seen:continue
        queue=[u];seen.add(u);twice=teeth=0;open_end=False
        for x,y in queue:
            marked=(x,y) in X
            teeth+=marked and (x in (1,N-2) or 3*j+y in (1,N-2))
            open_end|=(y==0 and j>0) or (y==5 and j+2<k)
            for v in ((x+1,y),(x-1,y),(x,y-1),(x,y+1)):
                if 0<=v[0]<N and 0<=v[1]<6 and (marked or v in X):
                    twice+=1
                    if v not in seen:seen.add(v);queue.append(v)
        assert twice==2*(len(queue)-1) and teeth<=1 and (teeth or open_end)
    assert value==sum((1+(h==0 and j==0 or h==1 and j==k-2))*
                      (3*k-sum(y//3==h for _,y in X)) for h in (0,1))
    x=3*(i+1);types=[]
    for y in range(6):
        a,b,c,d=((x+t,y) in X for t in (-2,-1,0,1))
        types.append(1 if b and c else 2 if a and not b and c else 3 if b and not c and d else 0)
    assert [sum(v<<(2*t) for t,v in enumerate(types[b:b+3])) for b in (0,3)]==[sym(A),sym(B)]
    return value
