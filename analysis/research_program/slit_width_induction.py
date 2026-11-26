"""Look for inductive inclusion of guarded slit languages, not equal scalar optima."""
from collections import defaultdict
from .finite_cap_language import extend,reduce_nfa
from .ranked_slit_prices import ALL,ZERO,EMPTY,compatible


def contains(big,small):
    if big is ALL or not small[1] or big is small:return True
    a,f=small;b,g=big;todo=[(0,0)];seen=set(todo)
    for x,y in todo:
        if x in f and y not in g:return False
        for c,u in a[x].items():
            t=(u,b[y].get(c,-1) if y>=0 else -1)
            if t not in seen:seen.add(t);todo.append(t)
    return True


def phase(t,clip):return t if t<clip else clip+(t-clip)%10


def widen(L,look,limit):
    if look is None or L is ALL or not L[1]:return L
    a,f=L;colors=[int(i in f) for i in range(len(a))]
    for _ in range(look):
        tab={};new=[tab.setdefault((i in f,tuple(sorted((c,colors[v]) for c,v in row.items()))),len(tab))
                    for i,row in enumerate(a)]
        if new==colors:return L
        colors=new
    # Merge similar states, keeping *every* arc. The quotient is an
    # NFA and can only enlarge the accepted language.
    rows=[defaultdict(set) for _ in range(max(colors)+1)]
    for i,row in enumerate(a):
        for c,v in row.items():rows[colors[i]][c].add(colors[v])
    return reduce_nfa(rows,{colors[i] for i in f},limit)


def cut_test(layers,get,a,b,clip,ceiling,wired):
    bad=[]
    for t1 in (range(a+1) if not wired else [a]):
        for t2 in (range(b+1) if not wired else [b]):
            t=t1+t2
            if not t:continue
            # 5B >= 4t+32 for disconnected caps; B>=6 for a
            # connected cap. Only B=2t (mod 4) can be physical.
            bmax=(4*t+31)//5 if t>=2 else 2
            bmax-=(bmax-2*t)%4
            cap=bmax-4*t1//5-4*t2//5
            u,v=phase(t1,clip),phase(t2,clip)
            lb=layers[a][u][0];rb=layers[b][v][0]
            for z in range(lb,cap-rb+1):
                if compatible(get(a,u,z),get(b,v,cap-z)):
                    bad.append((t1,t2,z,cap-z));break
    return bad


def attempt(end=28,clip=2,ceiling=5,limit=1500,wired=False,look=None,verbose=True,oracle=extend):
    # Slice coordinate z=B-floor(4t/5), t=number of retained contacts.
    # Above ceiling use a safe relaxation. Below the first nonempty
    # slice use EMPTY. A period is only reported if *every* slice is
    # contained, including the floors and the implicit upper tail.
    layers=[{0:(0,[])}];intern={}
    def pack(L):
        if not L[1]:return EMPTY
        sig=tuple(tuple(sorted(r.items())) for r in L[0]),tuple(sorted(L[1]))
        return intern.setdefault(sig,L)
    def get(n,t,z):
        data=layers[n].get(t)
        if data is None or z<data[0]:return EMPTY
        if not n:return ZERO
        return data[1][z-data[0]] if z<ceiling else ALL
    for n in range(1,end+1):
        prev=layers[-1];inc=defaultdict(list)
        for s,(floor,_) in prev.items():
            for drop in ((0,) if wired else (0,1)):
                t=phase(s+1-drop,clip)
                delta=4*(s+1-drop)//5-4*s//5
                inc[t].append((s,drop,delta,floor))
        cur={}
        for t,src in inc.items():
            floor=min(a-d for _,_,d,a in src);vec=[];low=None
            for z in range(floor,ceiling):
                opts={}
                for s,drop,delta,a in src:
                    for v in range(a,min(ceiling,z+delta)+1):
                        L=get(n-1,s,v)
                        if not L[1]:continue
                        w=z+delta-v
                        key=id(L),drop
                        if key not in opts or opts[key][1]<w:opts[key]=L,w,bool(drop)
                try:
                    L=pack(widen(oracle(list(opts.values()),'L' if n==1 else '',limit),look,limit))
                    if len(L[0])>limit//4:L=ALL
                except AssertionError as e:
                    if not(e.args and isinstance(e.args[0],tuple) and e.args[0][0] in ('product cap','subset cap')):raise
                    L=ALL
                if L[1] and low is None:low=z
                if low is not None:vec.append(L)
            cur[t]=(ceiling if low is None else low,vec)
        layers.append(cur)
        def included(k):
            for t,(a,_) in cur.items():
                if t not in layers[k]:return False
                for z in range(a,ceiling):
                    if not contains(get(k,t,z),get(n,t,z)):return False
            return True
        # A 10-triple block may be added to one of the two halves.
        # With 5 per half the normalized phase has period 10 in t,
        # so also try continuation after two steps of five per half.
        ok=n>10 and included(n-10)
        if verbose:print('prefix',n,'floors',sorted((t,a) for t,(a,_) in cur.items()),'included at -10',ok,flush=True)
        if ok and n>=28:return layers,get,n-10
    return layers,get,None


def prove(vertex=False):
    """Validate a *one-triple* invariant. Ten repetitions are then immediate."""
    from .slit_inclusion_check import product_checker
    from .finite_cap_language import transfer
    oracle=extend
    if vertex:
        from .cap_vertex_arrows import transfer,extend_vertex as oracle
    clip,ceiling=2,5
    layers,get,_=attempt(65,clip,ceiling,1500,False,None,False,oracle)
    def closure(n):
        cur=layers[n];prev=layers[n-1]
        return all(t in prev and all(contains(get(n-1,t,z),get(n,t,z)) for z in range(a,ceiling))
                   for t,(a,_) in cur.items())
    K=next(i-1 for i in range(13,len(layers)) if closure(i))
    print('stationary prefix at',K,'retained classes',len(layers[K]),flush=True)
    # Check the generated tables as mere conjectures. No determinization,
    # heuristic state limit, or assumed positivity of a bulk price here.
    image,count=product_checker(transfer,ALL)
    for old,new in [*((n-1,n) for n in range(1,K+1)),(K,K)]:
        for s,(lb,_) in layers[old].items():
            for drop in (0,1):
                t=phase(s+1-drop,clip);delta=4*(s+1-drop)//5-4*s//5
                assert t in layers[new]
                for z in range(layers[new][t][0]-1,ceiling):
                    out=get(new,t,z)
                    for v in range(lb,z+delta+1):
                        image(get(old,s,v),bool(drop),'L' if old==0 else '',z+delta-v,out)
    # Independently test the terminal products, using the actual integer
    # forbidden bonus rather than the normalized price cutoff in cut_test.
    pairs=0
    for n in range(4,K+1):
        for i in range(3):
            for j in range(n+1):
                t=i+j
                if not t:continue
                # Effective wired bonus b-j_actual=(2*t-B)/4.
                # At t>=2 want b-j_actual <= floor((3*t-16)/10).
                forbidden=0 if t==1 else (3*t-16)//10+1
                budget=2*t-4*forbidden-4*i//5-4*j//5
                u,v=phase(i,clip),phase(j,clip)
                for z in range(layers[2][u][0],budget-layers[n][v][0]+1):
                    assert not compatible(get(2,u,z),get(n,v,budget-z)),(n,i,j,z)
                pairs+=1
    # Every larger retained count has a representative in this final
    # prefix. Adding ten retained teeth raises the allowable raw B by
    # eight and the prefix normalization by eight, leaving the test fixed.
    assert K>=clip+9 and set(layers[K])==set(range(clip+10))
    print('passed',count(),'product inclusion checks including induction seam;',
          pairs,'terminal rank pairs; all widths r>=6',flush=True)
    return K


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--end',type=int,default=28)
    p.add_argument('--clip',type=int,default=2);p.add_argument('--ceiling',type=int,default=5)
    p.add_argument('--limit',type=int,default=1500);p.add_argument('--wired',action='store_true')
    p.add_argument('--look',type=int)
    p.add_argument('--prove',action='store_true');p.add_argument('--vertices',action='store_true')
    a=p.parse_args()
    if a.prove:prove(a.vertices)
    else:
        layers,get,k=attempt(a.end,a.clip,a.ceiling,a.limit,a.wired,a.look)
        for i,j in [(17,18),(17,28)]:
            if j<len(layers):
                bad=cut_test(layers,get,i,j,a.clip,a.ceiling,a.wired);print('split',i,j,'open pairs',len(bad),bad[:12])
