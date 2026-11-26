"""Square price for independently chosen recurrent straight-arm profiles."""
from itertools import product,combinations_with_replacement
import subprocess
import ast
from functools import lru_cache

MASKS=(1,9,73,509,489,329)
def corners(ranked=True):
    t={}
    for a,b in combinations_with_replacement(MASKS,2):
        out=subprocess.check_output(['target/collar_bend','critical-ranks' if ranked else 'critical-corner',str(a),str(b)],text=True)
        z=tuple(ast.literal_eval(out)) if ranked else int(out)
        t[a,b]=t[b,a]=z
    return t

def options(m):
    # Normal-arm mask counts only the scored outer nine sites. Bit nine
    # is independently free at every third (high) tip.
    yield ('bar',0,3*m,0,0,0,73,73)
    for tag,(lo,hi) in enumerate(zip(MASKS[:3],MASKS[3:])):
        for first in range(3):
            p=len(range(first,m,3));tail=m-1-(first+3*(p-1))
            z=p*hi.bit_count()+(m-p)*lo.bit_count()
            yield (str(tag),first,z,p,first,tail,hi if first==0 else lo,hi if tail==0 else lo)

def price(n,table,only=None,collect=None):
    from .dense_joint_collar import upper
    m=n-20;s=n-18;choices=list(options(m));maxima={};wits={}
    @lru_cache(None)
    def glue(pairs,room):
        if isinstance(table[pairs[0]],int):return sum(table[pair] for pair in pairs)
        d={0:0}
        for pair in pairs:
            e={}
            for r,z in d.items():
                for j,w in enumerate(table[pair]):
                    if w>=0 and j+r<=room:e[r+j]=max(e.get(r+j,-1000),z+w)
            d=e
        return max(d.values())
    for shape in product(choices,repeat=4):
        ids=[i for i,a in enumerate(shape) if a[0]!='bar'];k=len(ids)
        if k==0 or only is not None and k!=only:continue
        p=sum(a[3] for a in shape);joins=0
        for j,i in enumerate(ids):
            nxt=ids[(j+1)%k]
            joins+=shape[i][5]<2 and shape[nxt][4]<2
        core_components=p-joins-k+1
        loss_teeth=sum((shape[i][4]==0)+(shape[i][5]==0) for i in ids)
        through=max(int(i in ids and i+2 in ids and (shape[i][1]+shape[i+2][1])%3==(m-1)%3) for i in range(2))
        pairs=tuple(sorted(tuple(sorted((shape[i][7],shape[(i+1)%4][6]))) for i in range(4)))
        room=sum(3 if a[0]=='bar' else int(a[0])+1 for a in shape)-1
        bend=glue(pairs,room)
        ub=(s*s+3*sum(a[2] for a in shape)+m*(4-k)+bend+loss_teeth-core_components+through)//3
        def crossings(a):
            if a[0]=='bar':return 0
            return a[3]-(int(a[4]==0)+int(a[5]==0) if a[0]=='2' else 0)
        gain=max(crossings(shape[i])+crossings(shape[(i+1)%4]) for i in range(4))
        ub=min(ub,upper(n+1)-gain)
        if k==1:
            # From the retained core erase its two normal-side corners
            # and attach pitch, blank, full. Widen by blank, blank, bar.
            # The isolated new bar contributes an extra end pitch site.
            crop=upper(s+3)-(2*s+p+2)
            ub=min(ub,sum(a[2] for a in shape)+bend//3+crop)
        if k==2 and (ids[0]+2)%4==ids[1]:
            # Repeat the retained square horizontally on its two solid
            # side bars after erasing their four corners. Both normal
            # arms root all their high sites, even unmarked tip sites.
            pitch=(s-1)//3
            inner=(s+(s+1)*pitch-p if through else
                   s-2+s*pitch+(6*pitch-7*(p-2))//10)
            # The previous corner table paid two for a core corner;
            # full cost here is three. At most four units remain.
            ub=min(ub,sum(a[2] for a in shape)+(bend+4)//3+inner)
            if through:
                chi0=2 if shape[ids[0]][1]==2 else -1
                rc=p-1+(6*p-8-4*chi0+3)//4
            else:
                # Measure column phase from the first normal side; the
                # opposite side is traversed in the reverse direction.
                phases={(1+shape[ids[0]][1])%3,(-1-shape[ids[1]][1])%3}
                assert len(phases)==2
                chi0=1 if 0 in phases else -2
                rc=p-1+(6*p-1-4*chi0+4)//5
            ub=min(ub,sum(a[2] for a in shape)+(bend+s*s+4*s-2*p-rc)//3)
        if collect is not None:collect[tuple((a[0],a[1]) for a in shape)]=ub
        if ub>maxima.get(k,-1):maxima[k]=ub;wits[k]=[(a[0],a[1]) for a in shape]
    return maxima,wits
if __name__=='__main__':
    from .dense_joint_collar import comb
    t=corners();print('corner table',[t[a,b] for a,b in combinations_with_replacement(MASKS,2)],flush=True)
    for n in range(103,133,3):
        all_shapes={};z,_=price(n,t,collect=all_shapes);assert max(z[3],z[4])<=comb(n)
        same=[v for sh,v in all_shapes.items() if sh[0][0]==sh[2][0]=='bar'
              and sh[1][0]!='bar' and sh[3][0]!='bar' and (sh[1][1]+sh[3][1])%3==(n-21)%3]
        assert max(same)<=comb(n)
        print(n,'upper by number of normal arms',z,'comb',comb(n),flush=True)
