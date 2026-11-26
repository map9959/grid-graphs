"""One-gap full-board decision: project local charges and color perimeter attachments."""
from functools import lru_cache
from hashlib import sha256
from itertools import combinations,product
from pathlib import Path
import subprocess,sys
from .defect_window import table,DIR
from .odd_frames import frame
from .tight_corner_sat import cover
from .extend_forest_28 import verify

def generate(n,stem,dual=False):
    from pysat.card import CardEnc
    assert n>=119 and (n-119)%42==0
    typ,patch,star=table(n)
    def bit(i,j):return 1+i*n+j
    def boundary(i,j):return min(i,j,n-1-i,n-1-j)==0
    words=[(0,)+w for w in product((1,3),repeat=3)]
    frames=[frame(n,w) for w in words]
    path={(0,0):-1};q=list(path)
    for i,j in q:
        for d,(a,b) in enumerate(DIR):
            p=i+a,j+b
            if p in frames[0] and boundary(*p) and p not in path and (frames[0][i,j] or frames[0][p]):
                path[p]=(d+2)%4;q.append(p)
    assert len(path)==4*n-4
    # Arrow per direction; label of a forced branch is its attachment's
    # perimeter side. Remove perimeter-perimeter edges before propagating.
    def arc(i,j,d):return n*n+4*(bit(i,j)-1)+d+1
    def color(i,j,k):return 5*n*n+2*(bit(i,j)-1)+k+1
    top=7*n*n;f=stem.with_suffix('.cnf').open('w');f.write(' '*90+'\n')
    N=0
    def put(*cl):
        nonlocal N
        f.write(' '.join(map(str,cl))+' 0\n');N+=1
    sels=list(range(top+1,top+9));top+=8;put(*sels)
    for u in frames[0]:
        lits=[bit(*u)*(1 if m[u] else -1) for m in frames]
        if len(set(lits))==1:put(lits[0])
        else:
            for s,l in zip(sels,lits):put(-s,l)
    sites=[(2,d) for d in range(5,n-5,3)]+[(d,2) for d in range(5,n-5,3)]
    flags={p:top+k+1 for k,p in enumerate(sites)};top+=len(flags)
    card=CardEnc.equals(list(flags.values()),1,top_id=top,encoding=1);top=card.nv
    for cl in card.clauses:put(*cl)
    @lru_cache(None)
    def cubes(tab):
        return [[(s,-1 if v>>s&1 else 1) for s in range(len(tab).bit_length()-1) if m>>s&1]
                for m,v in cover(tab)]
    def forbid(vs,tab,*guard):
        for row in cubes(tab):put(*guard,*(vs[s]*k for s,k in row))
    @lru_cache(None)
    def patchbad(t):return tuple(v!=0 for v in patch(t))
    @lru_cache(None)
    def starbad(t,ds,d,root):return tuple(v!=0 for v in star(t,ds,d,root,len(ds)==2))
    for i,j in product(range(n),repeat=2):
        v=bit(i,j)
        if max(i,j)<n-2:
            vs=[bit(i+a,j+b) for a,b in product(range(3),repeat=2)]
            forbid(vs,patchbad(typ(1,i,j)))
        ds=tuple(d for d,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n)
        neighbors=[bit(i+DIR[d][0],j+DIR[d][1]) for d in ds]
        cross=[v,*neighbors];arcs=[arc(i,j,d) for d in ds];root=(i,j)==(0,0)
        flag=flags.get((i,j))
        if flag:
            for z in cross:put(-flag,-z)
            put(*cross,flag)
        else:put(*cross)
        for a,b in combinations(arcs,2):put(-a,-b)
        if (i,j) in path:
            for d,a in zip(ds,arcs):put(a if d==path[i,j] else -a)
            side=0 if i==0 else 1 if j==n-1 else 2 if i==n-1 else 3
            if dual>=2:side^=((i+j)//3)%4
            for k in range(2):put(color(i,j,k)*(1 if side>>k&1 else -1))
        if not root:put(*arcs,*([flag] if flag else []))
        for d,a in zip(ds,arcs):
            # A charged center has no arc, so every outgoing arc has zero charge.
            forbid(cross,starbad(typ(0,i,j),ds,d,root),-a)
        for d in (0,1):
            if d not in ds:continue
            x,y=i+DIR[d][0],j+DIR[d][1];w=bit(x,y)
            a,b=arc(i,j,d),arc(x,y,d+2)
            put(-a,-b);put(-a,v,w);put(-b,v,w);put(-v,a,b);put(-w,a,b)
            if boundary(i,j) and boundary(x,y):continue
            for k in range(2):
                c,h=color(i,j,k),color(x,y,k)
                for lit in (v,w):put(-lit,-c,h);put(-lit,c,-h)
    if dual:
        # All perimeter edges but the gap are forced. The complement of
        # any primal forest connects all faces to the exterior, through
        # the gap at (0,1)--(0,2). Root a dual tree in its incident face.
        m=n-1
        def dart(i,j,d):return top+5*(m*i+j)+1+d
        for i,j in product(range(m),repeat=2):
            ds=[d for d,(a,b) in enumerate(DIR) if 0<=i+a<m and 0<=j+b<m]
            arcs=[dart(i,j,d) for d in ds]
            if (i,j)==(0,1):
                for a in arcs:put(-a)
            else:put(*arcs)
            for a,b in combinations(arcs,2):put(-a,-b)
            endpoints=[((i,j+1),(i+1,j+1)),((i+1,j),(i+1,j+1)),
                       ((i,j),(i+1,j)),((i,j),(i,j+1))]
            for d,a in zip(ds,arcs):
                for p in endpoints[d]:put(-a,-bit(*p))
                x,y=i+DIR[d][0],j+DIR[d][1]
                if d<2:
                    b=dart(x,y,d+2);put(-a,-b)
                    if dual>=2:
                        # Extend the primal tree by the edge from the
                        # isolate toward its side. Every remaining free
                        # edge MUST now occur in the rooted dual tree.
                        u,v=endpoints[d]
                        exc=flags.get(v) if (d==0 and v[0]==2 or d==1 and v[1]==2) else None
                        put(bit(*u),bit(*v),a,b,*([exc] if exc else []))
                        if exc:put(-exc,-a);put(-exc,-b)
                # The sheet of the outgoing direction changes on passing
                # between 3 and 0, and on no other non-reversing turn.
                # At the root no outgoing direction needs a sheet.
                if (x,y)==(0,1) or dual==3:continue
                h,k=dart(i,j,4),dart(x,y,4)
                turn={3:0,0:3}.get(d)
                if turn is None or not(0<=x+DIR[turn][0]<m and 0<=y+DIR[turn][1]<m):
                    put(-a,-h,k);put(-a,h,-k)
                else:
                    b=dart(x,y,turn)
                    put(-a,b,-h,k);put(-a,b,h,-k);put(-a,-b,-h,-k);put(-a,-b,h,k)
        top+=5*m*m
        if dual==3:
            # Temperley matching: all nodes of the (2n-1)-square except
            # NW are matched. The XOR from a concrete reference tiling is
            # even at every node, hence is the boundary of a set of cells.
            # One common set of spins enforces ALL these parity cuts.
            dual_top=top-5*m*m
            def dbit(i,j,d):return dual_top+5*(m*i+j)+1+d
            h=2*n-1;base=top
            def spin(i,j):
                if 0<=min(i,j) and max(i,j)<h-1 and (i or j):
                    return base+1+i*(h-1)+j
                return 0
            top+=(h-1)**2
            def match(i,j,d): # fine-grid black node to adjacent edge slot
                nonlocal top
                if i%2:
                    I,J=i//2,j//2
                    x,y=I+DIR[d][0],J+DIR[d][1]
                    if not(0<=x<m and 0<=y<m):return (I,J,d)==(0,1,3)
                    return dbit(I,J,d)
                I,J=i//2,j//2
                var=arc(I,J,d);exc=flags.get((I,J))
                if exc and ((I==2 and d==3) or (J==2 and d==2)):
                    top+=1;put(-exc,top);put(-var,top);put(exc,var,-top);return top
                return var
            for i,j in product(range(h),repeat=2):
                if (i+j)%2 or (i,j)==(0,0):continue
                for d,(a,b) in enumerate(DIR):
                    x,y=i+a,j+b
                    if not(0<=x<h and 0<=y<h):continue
                    p,q=min(i,x),min(j,y)
                    ref=(i==x==0 and q%2==1) or (j==y and p%2==1)
                    u=spin(p,q);v=spin(p-1,q) if i==x else spin(p,q-1)
                    w=match(i,j,d)
                    for a1,b1 in product((0,1),repeat=2):
                        if (not u and a1) or (not v and b1):continue
                        expected=bool(ref^a1^b1)
                        ls=([-u if a1 else u] if u else [])+([-v if b1 else v] if v else [])
                        if isinstance(w,bool):
                            if w!=expected:put(*ls)
                        else:put(*ls,w if expected else -w)
    f.seek(0);f.write(f'p cnf {top} {N}'.ljust(90));f.close()
    print('side',n,'frames',len(frames),'depth-two sites',len(flags),'variables',top,'clauses',N,flush=True)

def run(n,sec,dual=0):
    stem=Path(f'target/depth_two_board_{n}'+{0:'',1:'_dual',2:'_cotree',3:'_dimer'}[dual])
    generate(n,stem,dual)
    cnf=stem.with_suffix('.cnf');drat=stem.with_suffix('.drat')
    print('CNF sha256',sha256(cnf.read_bytes()).hexdigest(),flush=True)
    with stem.with_suffix('.log').open('w') as out:
        st=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(cnf),str(drat)],stdout=out).returncode
    if st==20:
        with stem.with_suffix('.check').open('wb') as out:
            subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(drat)],stdout=out,check=True)
        assert b's VERIFIED' in stem.with_suffix('.check').read_bytes()
        print('all frames and sites: s VERIFIED')
    elif st==10:
        model={int(x) for l in stem.with_suffix('.log').read_text().splitlines() if l.startswith('v ') for x in l[2:].split()}
        rows=[''.join('#' if 1+i*n+j in model else '.' for j in range(n)) for i in range(n)]
        stem.with_suffix('.marks').write_text('\n'.join(rows)+'\n')
        print('projected SAT, marks',sum(s.count('#') for s in rows),flush=True)
        try:score=verify(rows)
        except AssertionError:
            assert not dual
            print('cyclic projection; not a spanning tree');return
        print('physical replay',score)
    else:print('no decision',st)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
