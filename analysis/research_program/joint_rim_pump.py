"""Boundary-to-boundary relation for a replaceable middle piece of an annulus side."""
from functools import lru_cache
from .exit_pump import tables, assign, masks, DIR

def kernel(H,interior=False,row0=0,one_gap_star=False,patch_dir=None,star_dir=None):
    typ,patch,star=tables(119)
    # First processed column is 12. Its predecessor and all columns through
    # the final separator are bulk SIDE types, not corner types.
    cols=[b for b in range(1<<H) if interior or b&3==1]
    @lru_cache(None)
    def arcs(j,a,b,w):
        ans=set()
        for c in cols:
            if c&((b<<1)|(b>>1)):continue
            charges=[patch(typ(1,row0+r,j-1))[m] for r,m in enumerate(masks(a,b,c,H))]
            if patch_dir is None and any(charges):continue
            if patch_dir is not None and (any(q not in (0,72) for q in charges) or sum(charges)>72):continue
            for nw,dirs in assign(b,w,b|c,H):
                paid=int(any(charges))
                for r,out in enumerate(dirs[:-1]):
                    if interior and r==0:continue
                    ds=(0,1,2) if not r else (0,1,2,3)
                    nb=(c>>r&1,b>>(r+1)&1,a>>r&1,b>>(r-1)&1 if r else 0)
                    m=(b>>r&1)+sum(nb[s]<<(k+1) for k,s in enumerate(ds))
                    q=star(typ(0,row0+r,j),ds,out,False,False)[m]
                    if patch_dir is not None and (q or (r==0 and out!=patch_dir)):break
                    if one_gap_star and not r and out not in (0,2):break
                    if star_dir is not None and not r and out!=star_dir:break
                    if one_gap_star and r==2 and q==72:paid=j%(6 if star_dir is not None else 3)+1
                    elif not one_gap_star and not interior and not r and out==1 and q==72:paid=j%3+1
                    elif q:break
                else:ans.add((c,nw,paid))
        return ans
    @lru_cache(None)
    def extend(b,c,p,trim=False):
        # H permanent left ports, H current ports, H fresh vertices.
        par=list(p)+list(range(2*H,3*H))
        def root(i):
            while par[i]!=i:i=par[i]
            return i
        def link(i,j):
            u,v=root(i),root(j);par[u]=v;return u!=v
        lo=int(trim) if interior else 0;hi=H-int(trim)
        for i in range(lo,hi):
            if (b|c)>>i&1 and not link(H+i,2*H+i):return
            if i+1<hi and c>>i&3 and not link(2*H+i,2*H+i+1):return
        v=[root(i) for i in (*range(H),*range(2*H,3*H))]
        return tuple(v.index(x) for x in v)
    return cols,arcs,extend

def relation(H,one_gap_star=False,patch_dir=None,star_dir=None):
    cols,arcs,extend=kernel(H,one_gap_star=one_gap_star,patch_dir=patch_dir,star_dir=star_dir)
    initial=tuple(range(H))*2;dp={};nentry=0
    for a in cols:
        for b in cols:
            if a&((b<<1)|(b>>1)):continue
            for w in range(1<<H):
                if w&~(a|b) or not arcs(12,a,b,w):continue
                dp[a,b,w,initial,0]=1<<nentry;nentry+=1
    # Each bit independently labels one entry (previous marks, current
    # marks, current arrows to the previous column). Never union bits
    # across different endpoint partitions.
    early={}
    for t in range(94):
        if t>=9 and t%3==0:
            old=early.pop(t-42,None)
            if old is not None and dp==old:
                print(f'H={H}: length {t-42} = {t} for ALL {nentry} entry labels; '
                      f'{len(dp)} end records, {sum(x.bit_count() for x in dp.values())} entry/end pairs',flush=True)
                return t-42,t
            early[t]=dp
        nd={}
        for (a,b,w,p,used),labels in dp.items():
            for c,nw,pay in arcs(12+t%(6 if star_dir is not None else 3),a,b,w):
                if pay and used:continue
                v=extend(b,c,p)
                if v is not None:
                    k=b,c,nw,v,used or pay;nd[k]=nd.get(k,0)|labels
        dp=nd
    raise ValueError('no repeat established inside the replaceable interval')

if __name__=='__main__':
    import sys
    relation(int(sys.argv[1]),'--one-gap-star' in sys.argv,next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--patch-dir=')),None))
