"""Test the uncapped cross-seam inequalities with common row/column accounts."""
from .cross_seam_bound import all_bands,rowchart,push,BASE,sym
from .ordered_seam_price import packet_bill,rims

def spectrum(k,r,tabs,north,south,R,C,hot,trace=False):
    # Saturating counter only for a REQUIRED minimum. Never cap traffic.
    shift=C+4
    mask=sum(((1<<(C+1))-1)<<(a*shift) for a in range(C+1))
    def entry(w):
        a,b=w
        return (3-a.bit_count())*shift+3-b.bit_count()
    z=push(BASE,north,True,r)
    if z is None:return 0,None
    st={(north,z,min(hot,int(bool(sym(north))))):1<<entry(north)}
    hist=[st] if trace else None
    for j in range(k-1):
        table=tabs[rowchart(j,k)];nd={};end=j==k-2
        maxG=(1+(j==0))*R[j]+(1+end)*R[j+1]
        for (w,z,n),bits in st.items():
            for y,g in table.get(w,()):
                if g>maxG or end and y!=south or 6-y[0].bit_count()-y[1].bit_count()>R[j+1]:continue
                h=push(z,y,end,r)
                if h is None or end and 2 in h[2]:continue
                v=(bits<<entry(y))&mask
                if v:
                    key=y,h,min(hot,n+bool(sym(y)))
                    nd[key]=nd.get(key,0)|v
        st=nd
        if trace:hist.append(st)
    total=0
    for key,b in st.items():
        if key[-1]==hot:total|=b
    def recover(a,b):
        kbit=a*shift+b
        key=next(key for key,v in st.items() if key[-1]==hot and v>>kbit&1)
        path=[]
        for j in reversed(range(k-1)):
            y,h,n=key;path.append(y);kbit-=entry(y)
            bound=(1+(j==0))*R[j]+(1+(j==k-2))*R[j+1]
            key=next(p for p,v in hist[j].items() if v>>kbit&1 and
                     min(hot,p[-1]+bool(sym(y)))==n and
                     (c:=dict(tabs[rowchart(j,k)].get(p[0],())).get(y)) is not None and c<=bound
                     and push(p[1],y,j==k-2,r)==h)
        return [key[0],*reversed(path)]
    return total,recover if trace else None

def test(axis,k=207,q=83,D=1062,C=18):
    top=[16]+[48]*(q-2)+[16,4]+[6]*(k-q-1);bot=[192]*(k-2)+[128,8]
    R=[3]*k
    R[0]=sum(3-x.bit_count() for x in top);R[-1]=sum(3-x.bit_count() for x in bot)
    R[1:4]=[7,8,4];R[-8:-1]=[5]*7;R[4]+=D-sum(R)
    assert min(R)>=0 and sum(R)==D
    gs=all_bands(axis,k,q,top,bot);memo={};hist=[]
    hot_at={q-5} | (set(range(12,q-6,10)) if axis==1 else set())
    reach={a:1<<a for a in range(C+1)};shift=C+4;budget=(1<<(D+1))-1
    for i,tabs in enumerate(gs):
        r=rowchart(i,k);a=tuple(top[i:i+2]);b=tuple(bot[i:i+2])
        n,s=rims(r,q-i)
        assert n is None or a in n and b in s
        hot=6 if i in hot_at else 0
        key=r,a,b,hot,tuple(id(t) for t in tabs.values())
        if key not in memo:memo[key]=spectrum(k,r,tabs,a,b,R,C,hot)[0]
        s=memo[key];nd={}
        for l,v in reach.items():
            for h in range(C+1):
                if s>>(shift*l+h)&1:
                    val=v<<h & budget
                    if val:nd[h]=nd.get(h,0)|val
        hist.append((reach,s));reach=nd
        if not reach:
            print('no control at',i);return
    values=0
    for b in reach.values():values|=b
    print('axis',axis,'control prices up to target:',(values&-values).bit_length()-1,
          values.bit_count(),values.bit_length()-1,'budget',bool(values>>D&1),flush=True)
    if not values>>D&1:return
    h=next(h for h,v in reach.items() if v>>D&1);rem=D;d=[h]
    for reach,s in reversed(hist):
        rem-=h
        h=next(l for l,v in reach.items() if v>>rem&1 and s>>(shift*l+h)&1)
        d.append(h)
    d.reverse();assert rem==h and sum(d)==D
    groups={}
    for i,g in enumerate(gs):
        key=(rowchart(i,k),tuple(top[i:i+2]),tuple(bot[i:i+2]),6 if i in hot_at else 0,tuple(map(id,g.values())))
        groups.setdefault(key,[]).append(i)
    bill=excess=0;paths=[None]*(k-1)
    for (r,a,b,hot,_),inds in groups.items():
        g=gs[inds[0]]
        _,get=spectrum(k,r,g,a,b,R,C,hot,True)
        for i in inds:
            p=get(d[i],d[i+1]);paths[i]=p
            word=list(map(sym,p));J=sum(map(bool,word))
            assert J>=hot and all(sum(3-w[h].bit_count() for w in p)==d[i+h] for h in (0,1))
            costs=[dict(g[rowchart(j,k)][w])[y] for j,(w,y) in enumerate(zip(p,p[1:]))]
            assert all(v<=(1+(j==0))*R[j]+(1+(j==k-2))*R[j+1] for j,v in enumerate(costs))
            B=packet_bill(word);assert B<=d[i]+d[i+1]
            bill+=B;excess+=max(0,J-1)
            if i==q-5:
                from .seam_price_replay import replay
                for j in (0,next(j for j,s in enumerate(word[:-1]) if s),k-2):
                    assert replay(axis,k,q,i,j,p[j],p[j+1],top,bot)==costs[j]
                ordered=[(3*j+b,(s>>(2*b))&3) for j,s in enumerate(word) for b in range(3) if s>>(2*b)&3]
                print('cut',i,'hops',J,'first/last',ordered[:4],ordered[-4:],
                      'neighbor deficits',d[i:i+2],'cross price',sum(costs),flush=True)
    assert bill<=2*D-d[0]-d[-1]
    mismatch=sum(p[1]!=w[0] for x,y in zip(paths,paths[1:]) for p,w in zip(x,y))
    edge=sum(max(0,sum(bool(sym(w)) for w in paths[i])-1) for i in (1,k-3))
    assert 6*excess>=40+16*((k-39)//14)+(k-14)+edge
    print('packet bill',bill,'excess hops',excess,'disagreements in shared column masks',mismatch)
    return d,R,ordered

if __name__=='__main__':
    import sys
    test(*map(int,sys.argv[1:]))
