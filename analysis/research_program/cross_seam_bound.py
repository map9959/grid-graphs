"""Whole-board lower bound priced by an uncapped ordered seam word."""
from functools import lru_cache
from .ordered_seam_price import BASE,push,table,rowchart,rims,sym
from .ordered_ports import transpose

@lru_cache(None)
def ht(axis,r,j,d):
    # Change the sweep direction but retain the physical north-star catalogue.
    out={}
    for (a,c),ys in table(axis,r,j,d).items():
        for b,e in ys:out.setdefault((a,b),[]).append((c,e))
    return out

@lru_cache(None)
def horizontal(z,w,end,j):
    return push(z,tuple(map(transpose,w)),end,j)

def band(axis,k,q,i,j):
    """Minimum whole two-row price for every realizable central plaquette."""
    j=rowchart(j,k);la=2 if j==0 else 1;lb=2 if j==37 else 1
    @lru_cache(None)
    def cost(w):return la*(3-w[0].bit_count())+lb*(3-w[1].bit_count())
    tabs=[ht(axis,rowchart(x,k),j,q-x) for x in range(k-1)]
    st={}
    for w in tabs[0]:
        z=horizontal(BASE,w,True,j)
        if z is not None:st[w,z]=cost(w)
    for x in range(i):
        new={}
        for (w,z),c in st.items():
            for y in tabs[x].get(w,()):
                g=horizontal(z,y,False,j)
                if g is not None:
                    key=y,g;v=c+cost(y)
                    if v<new.get(key,10**9):new[key]=v
        st=new
    @lru_cache(None)
    def rest(x,w,z):
        if x==k-1:return 0 if 2 not in z[2] else 10**9
        best=10**9
        for y in tabs[x].get(w,()):
            h=horizontal(z,y,x==k-2,j)
            if h is not None:best=min(best,cost(y)+rest(x+1,y,h))
        return best
    res={}
    for ((a,b),z),c in st.items():
        for y in tabs[i].get((a,b),()):
            g=horizontal(z,y,i==k-2,j)
            if g is None:continue
            h=rest(i+1,y,g)
            if h>=10**9:continue
            key=(a,y[0]),(b,y[1]);price=c+cost(y)+h
            if price<res.get(key,10**9):res[key]=price
    rest.cache_clear()
    return res

def graph(axis,k,q,i):
    r=rowchart(i,k);north,south=rims(r,q-i)
    tabs={}
    for j in range(k-1):
        jj=rowchart(j,k)
        if jj in tabs:continue
        t={}
        for (w,y),v in band(axis,k,q,i,j).items():t.setdefault(w,[]).append((y,v))
        tabs[jj]=t
    return r,north,south,tabs

def all_bands(axis,k,q,top,bot):
    """Forward/backward strip prices at every possible intersection. Pin the
    *entire* common north and south rims for this conditional test."""
    graphs=[{} for _ in range(k-1)]
    for j in sorted({rowchart(y,k) for y in range(k-1)}):
        la=2 if j==0 else 1;lb=2 if j==37 else 1
        @lru_cache(None)
        def cost(w):return la*(3-w[0].bit_count())+lb*(3-w[1].bit_count())
        ts=[ht(axis,rowchart(x,k),j,max(-4,min(5,q-x))) for x in range(k-1)]
        def allows(w,x):
            return (top is None or j!=0 or w[0]==top[x]) and (bot is None or j!=37 or w[1]==bot[x])
        st={}
        for w in ts[0]:
            if not allows(w,0):continue
            z=horizontal(BASE,w,True,j)
            if z is not None:st[w,z]=cost(w)
        fs=[st]
        for x,t in enumerate(ts):
            end=x==k-2;nd={}
            for (w,z),v in st.items():
                for y in t.get(w,()):
                    if not allows(y,x+1):continue
                    g=horizontal(z,y,end,j)
                    if g is None or end and 2 in g[2]:continue
                    d=v+cost(y);key=y,g
                    if d<nd.get(key,10**9):nd[key]=d
            st=nd;fs.append(st)
        rest=dict.fromkeys(st,0);intern={}
        for x in reversed(range(k-1)):
            nd={};p={};end=x==k-2
            for (w,z),v in fs[x].items():
                for y in ts[x].get(w,()):
                    if not allows(y,x+1):continue
                    g=horizontal(z,y,end,j);tail=rest.get((y,g))
                    if tail is None:continue
                    a=(w[0],y[0]);b=(w[1],y[1]);rem=tail+cost(y)
                    if rem<nd.get((w,z),10**9):nd[w,z]=rem
                    if v+rem<p.get((a,b),10**9):p[a,b]=v+rem
            signature=tuple(sorted(p.items()))
            if signature not in intern:
                t={}
                for (a,b),v in p.items():t.setdefault(a,[]).append((b,v))
                intern[signature]=t
            graphs[x][j]=intern[signature];rest=nd
    return graphs

def evaluate(G,k,word=None,reward=0,threshold=0,pair_weight=0):
    """Return the least sum(G) - reward*J, requiring at least threshold hops.
    The threshold counter saturates; no paths are discarded for exceeding it.
    """
    r,north,south,tabs=G
    st={}
    for w in tabs[0]:
        if north is not None and w not in north or word is not None and sym(w)!=word[0]:continue
        z=push(BASE,w,True,r);n=int(bool(sym(w)))
        if z is not None:st[w,z,min(n,threshold)]=(pair_weight*(6-sum(m.bit_count() for m in w))-reward*n,None)
    hist=[st]
    for j in range(k-1):
        new={};last=j==k-2;t=tabs[rowchart(j,k)]
        for prev,(v,_) in st.items():
            w,z,n=prev
            for y,c in t.get(w,()):
                if last and south is not None and y not in south or word is not None and sym(y)!=word[j+1]:continue
                g=push(z,y,last,r)
                if g is None or last and 2 in g[2]:continue
                inc=int(bool(sym(y)));key=y,g,min(threshold,n+inc)
                val=v+c-reward*inc+pair_weight*(6-y[0].bit_count()-y[1].bit_count())
                if key not in new or val<new[key][0]:new[key]=(val,prev)
        st=new;hist.append(st)
    choices=[key for key in st if key[-1]==threshold]
    if not choices:return None
    key=min(choices,key=lambda x:st[x][0]);v=st[key][0];path=[]
    for layer in reversed(hist):path.append(key[0]);key=layer[key][1]
    return v,tuple(reversed(path))

if __name__=='__main__':
    import sys
    ax,k,q,i=map(int,sys.argv[1:]);G=graph(ax,k,q,i)
    for t in (0,6):
        v,p=evaluate(G,k,threshold=t);print('threshold',t,'pair-price sum',v,'J',sum(bool(sym(w)) for w in p))
    v,p=evaluate(G,k,reward=5000);n=sum(bool(sym(w)) for w in p)
    print('maximum J',n,'pair-price sum',v+5000*n)
