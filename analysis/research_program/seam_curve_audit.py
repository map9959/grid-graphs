"""Independent count projections of the ordered-word tariff at a named cut."""
from subprocess import run
from .cross_seam_bound import all_bands,rowchart,push,BASE,sym,evaluate
from .ordered_seam_price import table,price

def curve(axis,k,q,i,top,bot):
    tabs=all_bands(axis,k,q,top,bot)[i]
    r=rowchart(i,k);north=tuple(top[i:i+2]);south=tuple(bot[i:i+2])
    z=push(BASE,north,True,r);assert z is not None
    def flags(w,prev):
        x=sym(w)
        return int(bool(x))+2*int(bool(x&42))+4*int(bool(x) and x!=prev)
    data=[str(k),'1 1',f'0 0 0 {flags(north,0)}'];st={(north,z):0}
    for j in range(k-1):
        nd={};es=[];end=j==k-2
        for (w,z),a in st.items():
            for y,c in tabs[rowchart(j,k)].get(w,()):
                if end and y!=south:continue
                g=push(z,y,end,r)
                if g is None or end and 2 in g[2]:continue
                b=nd.setdefault((y,g),len(nd));es.append(f'{a} {b} {c} {flags(y,sym(w))}')
        data.append(f'{len(nd)} {len(es)}');data.extend(es);st=nd
    out=run(['target/ordered_seam_curve'],input='\n'.join(data),text=True,capture_output=True,check=True)
    curves=[list(map(int,l.split())) for l in out.stdout.splitlines()]
    G=r,{north},{south},tabs
    assert all(min(v for v in vs if v>=0)==evaluate(G,k)[0] for vs in curves)
    assert min(v for v in curves[0][6:] if v>=0)==evaluate(G,k,threshold=6)[0]
    return curves

def cheap_train(axis):
    # A zero-price, one-direct-hop homogeneous step that can repeat at
    # arbitrary transverse heights without changing the frontier.
    v,p=price(axis,7,39,12,reward=40)
    assert sum(bool(sym(w)) for w in p)==38 and sum(6-a.bit_count()-b.bit_count() for a,b in p)==5
    z=BASE
    for j,w in enumerate(p):
        z=push(z,w,j in (0,38),7)
        if j==18:
            assert w in table(axis,7,7,5)[w] and push(z,w,False,7)==z
            assert sym(w) and not sym(w)&42 and 6-w[0].bit_count()-w[1].bit_count()==0
    assert 2 not in z[2]

def check():
    run(['rustc','-O','src/bin/ordered_seam_curve.rs','-o','target/ordered_seam_curve'],check=True)
    k=207;q=83;i=78;D=1062
    top=[16]+[48]*(q-2)+[16,4]+[6]*(k-q-1);bot=[192]*(k-2)+[128,8]
    for ax in (1,2):
        cheap_train(ax)
        for name,vs in zip(('hops','skips','packets'),curve(ax,k,q,i,top,bot)):
            within=[n for n,v in enumerate(vs) if 0<=v<=2*D]
            alln=[n for n,v in enumerate(vs) if v>=0]
            over=[n for n in alln if vs[n]>2*D]
            print('axis',ax,name,'max within budget',max(within),'unpriced max',max(alln),
                  'price at budget-max',vs[max(within)],'first excluded by price',over[:1],flush=True)
if __name__=='__main__':check()
