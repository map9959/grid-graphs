"""Four corners coupled by ALL overlapping two-tile tracks, independent inside cuts."""
from collections import defaultdict,deque
from functools import lru_cache
from itertools import combinations,product
from pathlib import Path
import subprocess,sys
from .tile_star_catalogue import catalogue
from .tile_circulation import edges

def run(n,axis,a,b,c,e,d,sec,width=2):
    from pysat.formula import CNF,IDPool
    K=(n-2)//3-1;B,types,_=catalogue(n,[d]);f=CNF();vp=IDPool();blocks=[];refs=[];domains={};recs=[]
    def outside(i,a,b):return i+1<a or i>=b
    for i,j in product(range(K),repeat=2):
        if not(outside(i,a,b) or outside(j,c,e)):continue
        p=types[i,j]
        if outside(i,a,b) and not outside(j,c,e):u,low,high=i,a,b
        elif outside(j,c,e) and not outside(i,a,b):u,low,high=j,c,e
        else:u=None
        starts=([-1] if u is None else
                [q for q in range(max(0,u-width+2),min(u,K+1-width)+1)
                 if q+width<=low or q>=high])
        for first in starts:
            blocks.append((i,j,p));r=[]
            for h,l in product(range(2),repeat=2):
                x,y=i+h,j+l;r.append((x,y,first if c<=y<e or a<=x<b else -1))
            refs.append(r)
        if p not in domains:
            domains[p]=[w for w in B[p] if all(not(min(2+3*x,2+3*y,n-3-3*x,n-3-3*y)>=14 and m&16 and m&(40 if axis==1 else 130))
                                                 for (x,y),m in zip(product((i,i+1),(j,j+1)),w))]
    tab={};lookup={};inc=defaultdict(list)
    for p,ls in domains.items():
        for h in range(4):
            z=defaultdict(int)
            for k,w in enumerate(ls):z[lookup.setdefault(edges(w)[h],len(lookup))]|=1<<k
            tab[p,h]=z
    for k,(x,y,z,t) in enumerate(refs):
        for h,key in enumerate(((x,y),(y,t),(z,t),(x,z))):inc[key].append((k,h))
    work=deque(range(len(blocks)));live=[(1<<len(domains[p]))-1 for _,_,p in blocks];inq=set(work)
    @lru_cache(None)
    def read(p,h,m):return sum(1<<q for q,v in tab[p,h].items() if v&m)
    @lru_cache(None)
    def allow(p,h,m):
        r=0
        for q,v in tab[p,h].items():
            if m>>q&1:r|=v
        return r
    while work:
        k=work.popleft();inq.remove(k);x,y,z,t=refs[k]
        for h,key in enumerate(((x,y),(y,t),(z,t),(x,z))):
            w=read(blocks[k][2],h,live[k])
            for l,s in inc[key]:
                if k==l:continue
                new=live[l]&allow(blocks[l][2],s,w)
                if new!=live[l]:
                    live[l]=new
                    if not new:print('empty track overlap',blocks[l][:2]);return
                    if l not in inq:inq.add(l);work.append(l)
    opts=defaultdict(set)
    def tile(u,m):return vp.id(('tile',u,m))
    def pair(u,v,m,p):
        tag=('pair',u,v,m,p)
        if tag not in vp.obj2id:
            z=vp.id(tag);x=tile(u,m);y=tile(v,p);f.extend([[-z,x],[-z,y],[z,-x,-y]])
        return vp.id(tag)
    for k,(x,y,z,t) in enumerate(refs):
        by=defaultdict(list)
        for h,(u,v,s,r) in enumerate(domains[blocks[k][2]]):
            if live[k]>>h&1:
                by[u,v].append(pair(z,t,s,r))
                for p,m in zip((x,y,z,t),(u,v,s,r)):opts[p].add(m)
        f.append([pair(x,y,u,v) for u,v in by])
        for (u,v),end in by.items():f.append([-pair(x,y,u,v),*end])
    def node(p,i,j):return (p,i,j)
    def mark(q):return vp.id(('m',q))
    def lab(q,h):return vp.id(('color',q,h))
    for p,ms in opts.items():
        vs=[vp.id() for _ in range((len(ms)-1).bit_length())];i,j,_=p
        for k,m in enumerate(sorted(ms)):
            z=tile(p,m)
            for h,v in enumerate(vs):f.append([-z,v*(1 if k>>h&1 else -1)])
            for dx,dy in product(range(3),repeat=2):
                q=node(p,dx,dy);v=mark(q);f.append([-z,v*(1 if m>>(3*dx+dy)&1 else -1)])
        for dx,dy in product(range(3),repeat=2):
            u,v=1+3*i+dx,1+3*j+dy
            if min(u,v,n-1-u,n-1-v)!=2:continue
            side=0 if u==2 else 1 if v==n-3 else 2 if u==n-3 else 3
            q=node(p,dx,dy)
            for h in range(2):f.append([-mark(q),lab(q,h)*(1 if side>>h&1 else -1)])
    # Equality on crop edges, deduplicated across the actual blocks. In
    # the ports-only transfer, the colors on unmarked joints can be
    # recovered from their incident marks after gluing.
    seen=set()
    for r in refs:
        vv=[node(r[2*(i//3)+j//3],i%3,j%3) for i,j in product(range(6),repeat=2)]
        for s,q in enumerate(vv):
            u,v=1+3*q[0][0]+q[1],1+3*q[0][1]+q[2]
            if min(u,v,n-1-u,n-1-v)<2:continue
            for delta,ok in ((1,s%6<5 and v<n-3),(6,s<30 and u<n-3)):
                if not ok:continue
                t=vv[s+delta]
                if (q,t) in seen:continue
                seen.add((q,t))
                for h in range(2):
                    x,y=lab(q,h),lab(t,h)
                    for guard in (mark(q),mark(t)):f.extend([[-guard,-x,y],[-guard,x,-y]])
    stem=Path(f'target/track_net_{n}_{axis}_{a}_{b}_{c}_{e}_{d}'+(f'_w{width}' if width!=2 else ''));fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
    print('network blocks',len(blocks),'live words',sum(v.bit_count() for v in live),'variables',f.nv,'clauses',len(f.clauses),flush=True)
    f.to_file(str(fn));f.clauses.clear()
    with stem.with_suffix('.log').open('wb') as fd:s=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(fn),str(pr)],stdout=fd).returncode
    if s==20:
        data=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],check=True,capture_output=True).stdout
        assert b's VERIFIED' in data;stem.with_suffix('.check').write_bytes(data);print('UNSAT s VERIFIED')
    else:print('track network SAT' if s==10 else 'UNKNOWN')
if __name__=='__main__':run(*map(int,sys.argv[1:]))
