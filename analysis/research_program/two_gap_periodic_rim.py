"""Quotient a 0011 collar by duplicating a 42-site block on both axes.

A SAT marking in this quotient is only a collar witness.  Lift it to
physical collars and check every original clause, including matching.
"""
from collections import Counter
from itertools import combinations,product
from pathlib import Path
from inspect import getclosurevars
import subprocess,sys
from pysat.formula import IDPool
from pysat.solvers import Solver
from .defect_window import table,window,DIR
from .odd_frames import frame
from .saturated_tile_phase import ROW,COL
from .tight_corner_sat import cover

def collar(n,h,base,cut,pool,consume):
    # The anchored prefix, 42-site block, and suffix have disjoint
    # coordinate names. Repeated blocks never contain the unique exit.
    def ax(x):
        if x<cut:return x
        if x<cut+42+n-base:return cut+(x-cut)%42
        return x-(n-base)
    dom={(i,j) for i,j in product(range(n),repeat=2) if min(i,j,n-1-i,n-1-j)<h}
    # Exits on the short north arc, at ordinary teeth, outside the block.
    ds=[d for d in range(5,n-5,3) if '--unfolded' in sys.argv or not cut<=d<cut+42+n-base]
    sites={('s',0,j) for j in ds}
    def emit(f,bit,flags,arc,sheet):
        assert set(flags)==sites
        vp=getclosurevars(bit).nonlocals['vp'];assert vp.top==f.nv
        # Map PySAT's unnamed sequential counter bits by order; the
        # ordered exit list is identical after pulling the suffix back.
        anon=0;ids=[0]
        for z in range(1,vp.top+1):
            obj=vp.obj(z)
            if obj is None:
                key=('counter',anon);anon+=1
            else:
                tag,i,j,*rest=obj;key=(tag,ax(i),ax(j),*rest)
            ids.append(pool.id(key))
        def add(ls):consume([ids[abs(x)]*(1 if x>0 else -1) for x in ls])
        for c in f.clauses:add(c)
        f.clauses.clear()
        def var(tag,i,j,*r):return pool.id((tag,ax(i),ax(j),*r))
        for u,v in frame(n,(0,0,1,1)).items():add([bit(*u)*(1 if v else -1)])
        # No isolates. All unused edges are owned by incident faces.
        for i,j in sorted(dom):
            for d,(a,b) in enumerate(DIR):
                if 0<=i+a<n and 0<=j+b<n:consume([-var('ext',i,j,d)])
            if min(i,j,n-1-i,n-1-j)<2:continue
            m=var('v',i,j)
            if min(i,j,n-1-i,n-1-j)==2:
                code={(2,2):1,(2,n-3):2}.get((i,j),0)
                for l in (0,1):consume([-m,var('color',i,j,l)*(1 if code>>l&1 else -1)])
            for x,y in ((i+1,j),(i,j+1)):
                if (x,y) not in dom or max(x,y)>n-3:continue
                for l in (0,1):
                    u,v=var('color',i,j,l),var('color',x,y,l)
                    for g in (m,var('v',x,y)):consume([-g,-u,v]);consume([-g,u,-v])
        axis=pool.id('axis');rules=[cover(tuple(m not in s for m in range(512))) for s in (ROW,COL)]
        if '--normal-axis' in sys.argv:consume([axis]) # allow vertical bonds, forbid horizontal
        for i,j in product(range(14,n-14,3),repeat=2):
            q=list(product(range(i-1,i+2),range(j-1,j+2)))
            if not all(p in dom for p in q):continue
            vs=[var('v',*p) for p in q]
            for flag,which,nb,words in ((pool.id(('axisrow',ax(i))),axis,(1,7),rules[0]),
                                      (pool.id(('axiscol',ax(j))),-axis,(3,5),rules[1])):
                consume([-flag,which])
                for b in nb:consume([-vs[4],-vs[b],flag])
                for mask,w in words:consume([-flag]+[(-z if w>>b&1 else z) for b,z in enumerate(vs) if mask>>b&1])
        return [pool.id(('s',0,ax(d))) for d in ds]
    return window(n,'rim',h,table(n),matching=True,domain=dom,defects=sites,
                  exit_only=True,emit_graph=emit)

def run(h,base,cut,budget):
    assert (base-35)%42==0 and cut>=max(h+5,20) and base-cut-42>=max(h+5,20)
    unfolded='--unfolded' in sys.argv
    ns=(base,) if unfolded else (base,base+42)
    pool=IDPool();dest=Path(f'target/two_gap_periodic_{base}_{h}_{cut}'+('_normal' if '--normal-axis' in sys.argv else '')+('_unfolded' if unfolded else ''))
    if '--replay' in sys.argv:
        for n in ns:collar(n,h,base,cut,pool,lambda c:None)
        raw=dest.with_suffix('.bits').read_bytes();top=pool.top
        assert len(raw)==(top+7)//8
        for n in (329,371):
            count=0
            def check(c):
                nonlocal count
                assert all(0<abs(v)<=top for v in c)
                assert any(bool(raw[(abs(v)-1)//8]&(1<<((abs(v)-1)%8)))==(v>0) for v in c)
                count+=1
            collar(n,h,base,cut,pool,check);print('stored lift',n,count,'clauses checked')
        return
    with Solver(name='cadical195') as sol:
        for n in ns:flags=collar(n,h,base,cut,pool,sol.add_clause)
        sol.conf_budget(budget);r=sol.solve_limited()
        if r is not True:
            print('quotient preliminary',r,flush=True)
            if r is False:
                p=dest.with_suffix('.cnf')
                with p.open('wb') as out:
                    out.write(b' '*63+b'\n');cnt=0
                    def write(c):
                        nonlocal cnt
                        cnt+=1;out.write((' '.join(map(str,c))+' 0\n').encode())
                    for n in ns:collar(n,h,base,cut,pool,write)
                    out.seek(0);out.write(f'p cnf {pool.top} {cnt}'.encode().ljust(63)+b'\n')
                pr=dest.with_suffix('.drat')
                rc=subprocess.run(['target/cadical/build/cadical','-t','120',str(p),str(pr)],stdout=subprocess.DEVNULL).returncode
                if rc==20:
                    out=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],check=True,capture_output=True).stdout
                    assert b's VERIFIED' in out;dest.with_suffix('.check').write_bytes(out);print('quotient s VERIFIED')
            return
        values=set(sol.get_model());print('quotient SAT; exit',[(pool.obj(z)) for z in flags if z in values],flush=True)
    dest.with_suffix('.bits').write_bytes(bytes(sum((1<<(j%8)) for j in range(i,min(i+8,pool.top)) if j+1 in values) for i in range(0,pool.top,8)))
    top=pool.top
    for n in ((base,) if unfolded else (base,base+42,base+84)):
        count=0
        def check(c):
            nonlocal count
            assert any(v in values for v in c);count+=1
        collar(n,h,base,cut,pool,check);assert pool.top==top
        print('lifted collar checked',n,h,count,flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:5]))
