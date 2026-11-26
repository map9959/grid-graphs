"""Local lemma for straightening any number of arbitrary five-row rail seams."""
from itertools import product

def check(h,patterns=None):
    best=[-1,-1]
    def visit(rows):
        if len(rows)<h:
            for m in range(8):
                if len(rows) in (0,h-1) and m&5:continue
                if rows and m&((rows[-1]<<1)|(rows[-1]>>1)):continue
                visit((*rows,m))
            return
        masks=(2,*rows,2);par=list(range(3*len(masks)))
        def root(x):
            while par[x]!=x:x=par[x]
            return x
        for i,r in enumerate(masks):
            for j in range(3):
                u=3*i+j
                for v,on in ((u-3,i>0 and (r|masks[i-1])>>j&1),(u-1,j>0 and r>>(j-1)&3)):
                    if on:
                        a,b=root(v),root(u)
                        if a==b:return
                        par[a]=b
        linked=int(root(1)==root(len(par)-2))
        best[linked]=max(best[linked],sum(m.bit_count() for m in rows))
        if patterns is not None:
            left,right=(sum(((v>>a)&1)<<i for i,v in enumerate(rows)) for a in (0,2))
            gain=sum(m.bit_count() for m in rows)+1-linked-h
            key=left,right
            if gain>patterns.get(key,(-1000,None))[0]:patterns[key]=gain,rows
    visit(())
    return best
def pair_bound(h):
    pat={};check(h,pat);N=1<<h
    # f is the best surplus through a complete rail module, indexed
    # by its right-column mask. First/last padding must be empty.
    f={r:v for (l,r),(v,_) in pat.items() if not l};seen={}
    for L in range(1,80):
        val=f[0];sig=tuple(sorted((r,g-val) for r,g in f.items()))
        if L<=10:print('modules',L,'upper on marks plus lost links minus straight marks',val)
        if sig in seen:
            z,b=seen[sig];print('exact relaxed profile repeats at',z,L,'shift',val-b);break
        seen[sig]=L,val
        left={l:max(g for r,g in f.items() if not l&((r<<1)|(r>>1))) for l in {p[0] for p in pat}}
        g={}
        for (l,r),(v,_) in pat.items():g[r]=max(g.get(r,-10000),left[l]+v)
        f=g
if __name__=='__main__':
    import sys
    if len(sys.argv)>1:pair_bound(int(sys.argv[1]));sys.exit()
    expected=[[-1,1],[0,2],[2,3],[3,4],[4,5],[6,6]]
    for h,v in enumerate(expected,1):
        b=check(h);assert b==v
        print('seam height',h,'maximum marks without/with local rail connection',*b)
