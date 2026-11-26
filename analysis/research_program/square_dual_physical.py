"""Independent verification of a periodic stencil directly on unpooled square sites."""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path
from math import lcm
import json

DIR=((0,1),(1,0),(0,-1),(-1,0))
P=tuple(product(range(3),repeat=2))


def trans(i,j,n,s):
    if s&4:j=n-1-j
    for _ in range(s%4):i,j=j,n-1-i
    return i,j


def legal(m):
    # Independent undirected DFS: do not consult the generating LP's
    # table of allowed masks.
    seen=set()
    for start in range(9):
        if start in seen:continue
        seen.add(start);todo=[(start,-1)]
        while todo:
            u,parent=todo.pop();i,j=divmod(u,3)
            for a,b in DIR:
                if not (0<=i+a<3 and 0<=j+b<3):continue
                v=3*(i+a)+j+b
                if v==parent or not (m>>u|m>>v)&1:continue
                if v in seen:return False
                seen.add(v);todo.append((v,u))
    return True


MASKS=tuple(m for m in range(512) if legal(m))
SYM={m:[sum(1<<(3*u+v) for q,(r,c) in enumerate(P) if m>>q&1 for u,v in [trans(r,c,3,g)])
        for g in range(8)] for m in MASKS}


def stencil(residue):
    return Path(__file__).with_name('square_dual_stencil'+(f'_r{residue}' if residue!=2 else '')+'.json')


def base_side(residue):
    return 19+(residue-19)%3


def generate(residue=2):
    # Decode the fit once. Verification below does not use its aggregated
    # matrix, objective, column names or row numbering.
    from .patch_square import relaxation
    from .repeating_patch_dual import filename
    path=filename(2,3,residue)
    _,pairs=json.loads(path.read_text());tags=[]
    relaxation(base_side(residue),6,pooled=2,period=3,tags=tags)
    d={tags[i][1]:Q(z)*tags[i][0] for i,z in pairs}
    dest=stencil(residue)
    dest.write_text(json.dumps([[k,str(z)] for k,z in sorted(d.items()) if z],separators=(',',':'))+'\n')


def inspect(n,residue=2,physical_costs=False):
    def tup(v):return tuple(map(tup,v)) if isinstance(v,list) else v
    coeff={tup(k):Q(v) for k,v in json.loads(stencil(residue).read_text())}
    scale=lcm(*(q.denominator for q in coeff.values()))
    y=Counter({k:int(q*scale) for k,q in coeff.items()})
    def ix(i,size,depth):
        return i if i<depth else depth+(i-depth)%3 if i<size-depth else 2*depth+3+i-size
    @lru_cache(None)
    def pos(r,c,size,depth):
        return (ix(r,size,depth),ix(c,size,depth))
    def sp(i,j):return pos(i,j,n,2)
    def pp(i,j):return pos(i,j,n-2,2)
    def fine(i,j,patch):
        return pos(i,j,n-2 if patch else n,5 if patch else 6)
    rows=Counter();copies=Counter();types={};right=0
    # Sum directly onto the orbit of each individual physical site. Using
    # sums (not averages) multiplies the local objective by orbit size.
    # This only identifies actual D4 images, never translated interior sites.
    @lru_cache(None)
    def staratoms(dirs):
        atoms=[]
        for f in range(2):
            for nb in product(range(2),repeat=len(dirs)):
                ls=[9]*4
                for d,b in zip(dirs,nb):ls[d]=b
                if any(ls[i]==ls[(i+1)%4]==1 for i in range(4)):continue
                for out in (-1,*(d for d in dirs if f or ls[d])):
                    images=[]
                    for g in range(8):
                        def turn(d):return ((2-d if g&4 else d)+(g&3))%4
                        bb=[9]*4
                        for d in dirs:bb[turn(d)]=ls[d]
                        images.append((f,tuple(bb),turn(out) if out!=-1 else -1))
                    atoms.append((f,ls,out,images))
        return atoms
    for i,j in product(range(n),repeat=2):
        t=sp(i,j);ft=fine(i,j,False)
        dirs=tuple(d for d,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n)
        right+=y['star norm',ft]
        if len(dirs)==2:
            assert y['corner',ft]<=0
            right+=y['corner',ft]
        positions=[trans(i,j,n,g) for g in range(8)];ref=min(positions)
        gs=[g for g,x in enumerate(positions) if x==ref]
        cover=[(q,pp(i-a,j-b),[d for d,(u,v) in enumerate(DIR) if 0<=a+u<3 and 0<=b+v<3])
               for q,(a,b) in enumerate(P) if 0<=i-a<n-2 and 0<=j-b<n-2]
        for f,ls,out,images in staratoms(dirs):
            lhs=y['star norm',ft]+(4*y['corner',ft] if out==-1 and len(dirs)==2 else 0)
            for d in dirs:
                a,b=DIR[d];u=sp(i+a,j+b);sgn=1 if d<2 else -1
                lab=(f,ls[d]) if d<2 else (ls[d],f)
                edge=lab+((sgn if out==d else -sgn) if f or ls[d] else 0,)
                lhs+=sgn*(y['s',t,u,d,edge] if d<2 else y['s',u,t,d-2,edge])
            for q,p,dirs2 in cover:lhs+=y['sp',p,t,q,(f,*(ls[d] for d in dirs2))]
            key='s',ref,min(images[g] for g in gs)
            rows[key]+=lhs-f*scale;copies[key]+=1
            if key not in types:types[key]=('s',min((fine(*z,False),images[g]) for g,z in enumerate(positions)))
    for i,j in product(range(n-2),repeat=2):
        t=pp(i,j);ft=fine(i,j,True);right+=y['patch norm',ft]
        positions=[trans(i,j,n-2,g) for g in range(8)];ref=min(positions)
        gs=[g for g,x in enumerate(positions) if x==ref]
        neigh=[(d,pp(i+a,j+b)) for d,(a,b) in enumerate(DIR) if 0<=i+a<n-2 and 0<=j+b<n-2]
        for m in MASKS:
            bits=[(m>>q)&1 for q in range(9)]
            lhs=y['patch norm',ft]
            for q,(a,b) in enumerate(P):
                event=(bits[q],*(bits[(a+u)*3+b+v] for u,v in DIR if 0<=a+u<3 and 0<=b+v<3))
                lhs-=y['sp',t,sp(i+a,j+b),q,event]
            for d,u in neigh:
                di,dj=DIR[d%2]
                overlap=tuple(bits[3*a+b] for a,b in P if (a>=di and b>=dj if d<2 else a<3-di and b<3-dj))
                lhs+=(y['pp',t,u,di,dj,overlap] if d<2 else -y['pp',u,t,di,dj,overlap])
            key='p',ref,min(SYM[m][g] for g in gs)
            rows[key]+=lhs;copies[key]+=1
            if key not in types:types[key]=('p',min((fine(*z,True),SYM[m][g]) for g,z in enumerate(positions)))
    assert min(rows.values())>=0, sorted(rows.items(),key=lambda x:x[1])[:1]
    ans=Q(right,scale)
    if residue==2:assert ans==Q(n*n,3)+Q(20*n,21)-Q(67,42)
    if n>=base_side(residue):
        j=(n-base_side(residue))//3
        assert n%3==residue and ans==sum(v*j**i for i,v in enumerate(symbolic(residue,False)))
    print("physical side",n,"unpooled orbit columns",len(rows),"minimum integer slack",min(rows.values()),
          "unrestricted upper",ans,flush=True)
    if physical_costs:
        return ans,{(t,(pos,*v) if t=='s' else (pos,v)):Q(w,copies[t,pos,v]*scale)
                    for (t,pos,v),w in rows.items()}
    family={}
    for key,value in rows.items():
        slack=Q(value,copies[key]*scale)
        assert family.setdefault(types[key],slack)==slack
    return family


def symbolic(residue=2,verbose=True):
    """Prove the RHS polynomial by counts per boundary side and phase."""
    vals=json.loads(stencil(residue).read_text())
    n0=base_side(residue)
    # n=20+3j. A 1D interior residue type gains exactly one site per step.
    poly=[Q(0)]*3
    for tag,v in vals:
        if tag[0]=='corner':poly[0]+=Q(v)
        if tag[0] not in ('star norm','patch norm'):continue
        patch=tag[0]=='patch norm';depth=5 if patch else 6;side=n0-2 if patch else n0
        def count(idx):
            if not depth<=idx<depth+3:return 1,0
            return (side-2*depth+2-(idx-depth))//3,1
        a,b=count(tag[1][0]);c,d=count(tag[1][1])
        for i,x in enumerate((a*c,a*d+b*c,b*d)):poly[i]+=Q(v)*x
    if residue==2:assert poly==[Q(2111,14),Q(300,7),Q(3)]
    if verbose:print(f"RHS coefficients in j=(n-{n0})/3:",*[str(x) for x in poly])
    return poly


if __name__=='__main__':
    import sys
    r=int(sys.argv[sys.argv.index('--residue')+1]) if '--residue' in sys.argv else 2
    n0=base_side(r)
    if '--generate' in sys.argv:generate(r)
    base=inspect(n0,r)
    for n in (n0+3,n0+18,n0+21):assert inspect(n,r)==base
    print("identical eight-image average on all",len(base),"symbolic atom/type orbits")
    symbolic(r)
