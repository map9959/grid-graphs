"""Rank-resolved all-height slit matching, with safe upward language relaxation."""
from .finite_cap_language import extend

ALL=([{a:0 for a in range(8)}],{0})
ZERO=([{0:0}],{0})
EMPTY=([{}],set())


def compatible(a,b):
    # Read the suffix from the right edge. Reverse both incident mark
    # bits and the direction of a present bond, never the row order.
    A,F=a;B,G=b
    if not F or not G:return False
    rev=lambda c:((c&1)<<1)|((c&2)>>1)|((4^(c&4)) if c&3 else 0)
    seen={(0,0)};ls=[(0,0)]
    for u,v in ls:
        if u in F and v in G:return True
        for c,w in A[u].items():
            t=B[v].get(rev(c))
            if t is not None and (w,t) not in seen:seen.add((w,t));ls.append((w,t))
    return False


def audit(limit=3000,span=18,oracle=extend,price=90,check=False):
    lower={};cache={};truncated=0
    def bound(n,g,j):
        if not 0<=j<=n:return 999
        if not n:return 0
        if (n,g,j) in lower:return lower[n,g,j]
        # A lower bound on each physical subinterval; use the best
        # split, allowing the least expensive distribution of j.
        z=max((min(bound(i,g,t)+bound(n-i,0,j-t) for t in range(max(0,j+i-n),min(j,i)+1))
               for i in range(1,n)),default=0)
        lower[n,g,j]=z;return z
    def lang(n,g,j,z):
        nonlocal truncated
        if z<bound(n,g,j):return EMPTY
        if n==0:return ZERO if g else ALL
        key=n,g,j,z
        if key in cache:return cache[key]
        # Expensive languages can only enlarge the test if replaced
        # by ALL. Tight subintervals remain checked independently.
        if z>bound(n,g,j)+4:return ALL
        opts={}
        for d in range(2):
            for v in range(bound(n-1,g,j-d),z+1):
                L=lang(n-1,g,j-d,v)
                if L[1] and (id(L),d) not in opts:opts[id(L),d]=(L,z-v,bool(d))
        try:
            a=oracle(list(opts.values()),'L' if n==1 and g else '',limit)
            if len(a[0])>limit//4:a=ALL;truncated+=1
            if not a[1]:a=EMPTY
        except AssertionError as e:
            if not(e.args and isinstance(e.args[0],tuple) and e.args[0][0] in ('product cap','subset cap')):raise
            a=ALL;truncated+=1
        cache[key]=a;return a
    for n in range(1,span+1):
        for g in (0,1):
            for j in range(n+1):
                z=bound(n,g,j)
                while not lang(n,g,j,z)[1]:z+=1;lower[n,g,j]=z
            print('block',n,'guard',g,'B lower',[bound(n,g,j) for j in range(n+1)],flush=True)
    print('language relaxations',truncated,flush=True)
    remaining=[];upper={};splits=[]
    for j in range(35):
        target=9 if not j else 34 if j==34 else (price+7*j)//10+1
        budget=70+2*j-4*target
        for n in range(1,35):
            other=35-n
            pairs=[(t,j-t) for t in range(max(0,j-other),min(n,j)+1)]
            if all(bound(n,1,t)+bound(other,1,u)>budget for t,u in pairs):break
            if max(n,other)>span:continue
            if not any(compatible(lang(n,1,t,z),lang(other,1,u,budget-z)) for t,u in pairs
                       for z in range(bound(n,1,t),budget-bound(other,1,u)+1)):break
        else:remaining.append(j);continue
        upper[j]=target-1;splits.append(n)
        print('rank',j,'excluded B <=',budget,'at split',n,'+',35-n,'=> b <=',target-1)
    print('remaining from rank-resolved windows',remaining)
    if not remaining:
        print('maximum paired square upper',3605+max(upper[i]+upper[j] for i in upper for j in upper if i+j<=34))
        if check:
            from .slit_inclusion_check import verify
            if oracle is extend:from .finite_cap_language import transfer
            else:from .cap_vertex_arrows import transfer
            verify(35,[upper[j]+1 for j in range(35)],splits,bound,lang,transfer,ALL,EMPTY)
    return remaining


if __name__=='__main__':
    import sys
    args=[int(s) for s in sys.argv[1:] if not s.startswith('--')]
    oracle=extend
    if '--vertices' in sys.argv:
        from .cap_vertex_arrows import extend_vertex as oracle
    assert not audit(*args,oracle=oracle,price=89 if '--tight' in sys.argv else 90,check='--check' in sys.argv)
