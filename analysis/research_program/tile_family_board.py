"""Exact seam support on the physical board, without pooled tile frequencies."""
from collections import defaultdict,deque,Counter
from itertools import product
from functools import lru_cache
from .tile_family_lp import projected,typ
from .tile_circulation import edges
import sys

def run(n,axis,star=5,cnf=False):
    k=(n-2)//3;K=k-1;coords=list(product(range(K),repeat=2));types=[]
    rg=next((s.split('=')[1] for s in sys.argv if s.startswith('--dist=')),None);cond={}
    if rg:
        from .tile_star_catalogue import catalogue
        lo,hi=map(int,rg.split(':'));step=3 if '--all-phases' in sys.argv else 6
        ds=list(range(lo,hi+1,step));assert lo%3==2 and ds[-1]==hi and 5<=lo<=hi<=n-6
        B,pt,cond=catalogue(n,ds)
    else:B=projected(3,star);ds=[star];pt={v:tuple(typ(i,K) for i in v) for v in coords}
    catalogs={};labels={};wordid={};marg={}
    for i,j in coords:
        p=pt[i,j];types.append(p)
        if p in catalogs:continue
        ls=[b for b in B[p] if all(not(min(2+3*(i+h),2+3*(j+l),n-3-3*(i+h),n-3-3*(j+l))>=14 and m&16 and m&(40 if axis==1 else 130))
                                    for (h,l),m in zip(product(range(2),repeat=2),b))]
        catalogs[p]=ls
        for side in range(4):
            tab=defaultdict(int)
            for z,b in enumerate(ls):
                e=edges(b)[side];v=wordid.setdefault(e,len(wordid));tab[v]|=1<<z
            marg[p,side]=tab
    @lru_cache(None)
    def mask(p,s,dom):return sum(1<<v for v,which in marg[p,s].items() if which&dom)
    @lru_cache(None)
    def allow(p,s,w):
        v=0
        for a,b in marg[p,s].items():
            if w>>a&1:v|=b
        return v
    open_north='--open-north' in sys.argv
    rim=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--rim=')),0)
    split=next((tuple(map(int,s.split('=')[1].split(':'))) for s in sys.argv if s.startswith('--tracks=')),None)
    def retained(i,j):
        if not split:return True
        a,b=split # omitted tile indices a,...,b-1; the corners keep both endpoints
        def outside(z):return z+1<a or z>=b
        def paired(z):return outside(z) and (z if z<a else z-b)%2==0
        return (outside(i) and outside(j)) or paired(i) or paired(j)
    dom=[(1<<len(catalogs[t]))-1 if (not open_north or coords[z][0]>=3) and
         (not rim or min(*coords[z],K-1-coords[z][0],K-1-coords[z][1])<rim) and retained(*coords[z]) else 0 for z,t in enumerate(types)]
    active={z for z,d in enumerate(dom) if d};work=deque(sorted(active));inq=set(work)
    while work:
        z=work.popleft();inq.remove(z);i,j=coords[z]
        for s,(x,y) in enumerate(((i-1,j),(i,j+1),(i+1,j),(i,j-1))):
            if not(0<=x<K and 0<=y<K):continue
            v=x*K+y
            if v not in active:continue
            p=types[v];m=dom[v]&allow(p,s^2,mask(types[z],s,dom[z]))
            if not m:
                print('no physical seam support',n,axis,'at',x,y,flush=True);return
            if m!=dom[v]:
                dom[v]=m
                if v not in inq:work.append(v);inq.add(v)
    @lru_cache(None)
    def patterns(p,d,h):return tuple(sorted({b[h] for z,b in enumerate(catalogs[p]) if d>>z&1}))
    mins=maxs=0;forced=Counter()
    for i,j in product(range(k),repeat=2):
        x=min(i,K-1);y=min(j,K-1);z=x*K+y;h=2*(i-x)+j-y
        if z not in active:continue
        ms=patterns(types[z],dom[z],h);a=min(m.bit_count() for m in ms);b=max(m.bit_count() for m in ms)
        mins+=3-b;maxs+=3-a
        forced[len(ms)]+=1
    print('side',n,'axis',axis,'live physical words',sum(d.bit_count() for d in dom),'forced tiles',forced[1],
          'independent deficit interval',mins,maxs,'target',5*k-1+(k-5)//7,flush=True)
    if '--roots' in sys.argv:
        from .tile_forced_tracks import forced
        return forced(n,types,catalogs,dom)
    if cnf:return encode(n,axis,star,types,catalogs,dom,ds,cond,rg)

def encode(n,axis,star,types,catalogs,dom,ds,cond,rg):
    from pysat.formula import CNF,IDPool
    from pathlib import Path
    import subprocess
    K=(n-2)//3-1;f=CNF();vp=IDPool()
    # Binding each tuple to its two row words and the lower and upper
    # masks gives a short trie, instead of one variable per plaquette.
    def tile(i,j,m):return vp.id(('tile',i,j,m))
    flags={d:vp.id(('star',d)) for d in ds} if rg else {}
    if flags:
        from itertools import combinations
        f.append(list(flags.values()));f.extend([[-a,-b] for a,b in combinations(flags.values(),2)])
    domains=defaultdict(set)
    for z,p in enumerate(types):
        if not dom[z]:continue
        i,j=divmod(z,K);by=defaultdict(set)
        for h,(a,b,c,d) in enumerate(catalogs[p]):
            if not dom[z]>>h&1:continue
            by[a,b].add((c,d))
            for dx,dy,w in ((0,0,a),(0,1,b),(1,0,c),(1,1,d)):domains[i+dx,j+dy].add(w)
        low={v for vs in by.values() for v in vs}
        def pair(x,y,a,b):
            tag='pair',x,y,a,b
            if tag not in vp.obj2id:
                s=vp.id(tag);v=tile(x,y,a);w=tile(x,y+1,b)
                f.extend([[-s,v],[-s,w],[s,-v,-w]])
            return vp.id(tag)
        f.append([pair(i,j,a,b) for a,b in sorted(by)])
        for (a,b),vs in sorted(by.items()):f.append([-pair(i,j,a,b),*[pair(i+1,j,c,d) for c,d in sorted(vs)]])
        if (i,j) in cond:
            for (a,b),vs in by.items():
                for c,d in vs:
                    take=cond[i,j][a,b,c,d]
                    if len(take)==len(ds):continue
                    g=[-pair(i,j,a,b),-pair(i+1,j,c,d)]
                    if len(take)<len(ds)//2:f.append(g+[flags[z] for z in take])
                    else:
                        for z in ds:
                            if z not in take:f.append(g+[-flags[z]])
    for (i,j),ms in domains.items():
        code=[vp.id() for _ in range((len(ms)-1).bit_length())]
        f.append([tile(i,j,m) for m in sorted(ms)])
        for k,m in enumerate(sorted(ms)):
            for h,u in enumerate(code):f.append([-tile(i,j,m),u if k>>h&1 else -u])
    rimtag=next(('_rim'+s.split('=')[1] for s in sys.argv if s.startswith('--rim=')),'')
    tracktag=next(('_tracks'+s.split('=')[1].replace(':','to') for s in sys.argv if s.startswith('--tracks=')),'')
    rimtag+=tracktag
    if '--all-phases' in sys.argv:rimtag+='_bothphase'
    fn=Path(f'target/physical_tile_{n}_{axis}_'+(rg.replace(':','to') if rg else str(star))+('_openN' if '--open-north' in sys.argv else '')+rimtag+'.cnf');pr=fn.with_suffix('.drat')
    colors=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--colors=')),0)
    if colors:
        # Delete the perimeter and the empty ring. No two distinct
        # marked boundary sites of the remaining crop can be connected.
        # Any hash of these roots is a valid necessary labeling.
        def mark(i,j):return vp.id(('mark',i,j))
        def label(i,j,h):return vp.id(('color',i,j,h))
        active={divmod(z,K) for z,v in enumerate(dom) if v}
        def linked(i,j,x,y):
            if not tracktag:return True
            u,v=(i-1)//3,(j-1)//3
            return any((p,q) in active and 1+3*p<=x<=6+3*p and 1+3*q<=y<=6+3*q
                       for p in (u-1,u) for q in (v-1,v))
        for (i,j),ms in sorted(domains.items()):
            for m in ms:
                z=tile(i,j,m)
                for a,b in product(range(3),repeat=2):
                    v=mark(1+3*i+a,1+3*j+b);f.append([-z,v if m>>(3*a+b)&1 else -v])
        for i,j in product(range(2,n-2),repeat=2):
            z=mark(i,j)
            if min(i,j,n-1-i,n-1-j)==2:
                side,dist=(0,j) if i==2 else (1,i) if j==n-3 else (2,j) if i==n-3 else (3,i)
                code=side+4*dist
                for h in range(colors):f.append([-z,label(i,j,h)*(1 if code>>h&1 else -1)])
            for x,y in ((i+1,j),(i,j+1)):
                if max(x,y)>n-3 or not linked(i,j,x,y):continue
                for h in range(colors):
                    u=label(i,j,h);v=label(x,y,h)
                    for guard in (z,mark(x,y)):f.extend([[-guard,-u,v],[-guard,u,-v]])
        fn=fn.with_name(fn.stem+f'_colors{colors}.cnf');pr=fn.with_suffix('.drat')
    if '--score' in sys.argv:
        from pysat.pb import PBEnc,EncType
        losses=[]
        for (i,j),ms in sorted(domains.items()):
            for h in (1,2):
                z=vp.id();losses.append(z)
                for m in ms:f.append([-tile(i,j,m),z if m.bit_count()<=h else -z])
        k=(n-2)//3;D=5*k-1+(k-5)//7
        assert all(1<=m.bit_count()<=3 for ms in domains.values() for m in ms)
        f.extend(PBEnc.equals(lits=losses,bound=D,top_id=vp.top,encoding=EncType.adder).clauses)
        fn=fn.with_name(fn.stem+'_score.cnf');pr=fn.with_suffix('.drat')
    cotree=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--dual=')),0)
    area=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--area=')),0)
    if area:
        from .tile_area import install
        assert '--score' not in sys.argv and '--open-north' not in sys.argv
        install(f,vp,n,domains,tile,flags,star,area)
        fn=fn.with_name(fn.stem+f'_area{area}.cnf');pr=fn.with_suffix('.drat')
    if '--root-flow' in sys.argv:
        from .tile_root_flow import install
        install(f,vp,n,domains,tile,flags,star)
        fn=fn.with_name(fn.stem+'_flow.cnf');pr=fn.with_suffix('.drat')
    if cotree:
        from .tile_cotree import install
        assert '--score' not in sys.argv and '--open-north' not in sys.argv
        install(f,vp,n,domains,tile,flags,star,cotree==2)
        fn=fn.with_name(fn.stem+f'_dual{cotree}.cnf');pr=fn.with_suffix('.drat')
    if '--replay' in sys.argv:s=10
    else:
        f.to_file(str(fn))
        seconds=next((s.split('=')[1] for s in sys.argv if s.startswith('--seconds=')),'120')
        with fn.with_suffix('.log').open('wb') as o:s=subprocess.run(['target/cadical/build/cadical','-t',seconds,str(fn),str(pr)],stdout=o).returncode
    f.clauses.clear()
    if s==20:
        q=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True,check=True).stdout
        assert b's VERIFIED' in q;fn.with_suffix('.check').write_bytes(q);print('physical tile relaxation s VERIFIED')
    elif s==10:
        from .odd_frames import frame
        from .extend_forest_28 import verify
        model={int(z) for line in fn.with_suffix('.log').read_text().splitlines() if line.startswith('v ') for z in line[2:].split()}
        if flags:print('selected star', [d for d,z in flags.items() if z in model])
        X={u for u,v in frame(n,(0,1,3,3)).items() if v}
        for (i,j),ms in domains.items():
            m,=[m for m in ms if tile(i,j,m) in model]
            X.update((1+3*i+a,1+3*j+b) for a,b in product(range(3),repeat=2) if m>>(3*a+b)&1)
        par={};E=rank=0
        def rt(u):
            while u in par:
                if par[u] in par:par[u]=par[par[u]]
                u=par[u]
            return u
        for i,j in product(range(n),repeat=2):
            u=i,j
            for v in ((i+1,j),(i,j+1)):
                if max(v)>=n or not (u in X or v in X):continue
                E+=1;a,b=rt(u),rt(v)
                if a==b:rank+=1
                else:par[a]=b
        print('physical tile model: marks',len(X),'forced edges',E,'cycle rank',rank,'components',n*n-E+rank)
        if not rank:
            rows=[''.join('#' if (i,j) in X else '.' for j in range(n)) for i in range(n)]
            print('physical spanning-tree completion',verify(rows))
            k=(n-2)//3
            if len(X)==3*k*k+7*k-(k-5)//7:fn.with_suffix('.tree').write_text('\n'.join(rows)+'\n')
    else:print('UNKNOWN')
if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2]),cnf=any(s in sys.argv for s in ('--sat','--replay')))
