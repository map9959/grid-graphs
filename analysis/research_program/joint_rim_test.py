"""Glue four actual strips at their H x H corners; check the entire induced forest."""
from itertools import product,combinations
from .exit_pump import tables,frame,rotate,DIR
from .square_dual_physical import trans
from .joint_rim_pump import relation
from .defect_window import window
from collections import Counter
from pathlib import Path
import subprocess

def test(H,shared=False,connector=False,cross=0):
    from pysat.solvers import Solver
    n=119
    if shared:
        from .shared_root_pump import check
        if cross:
            assert cross in (3,5) and H<=8
            start=(n-cross)//2
            # Insert 21 columns on each side of the central junction.
            radius=cross//2
            for l in (check(H,21,trimpath=radius),check(cross,21,True,start,radius)):
                assert 12+l<=start-2 and 69+l<=n-12
                assert 69>=start+cross+2
            L=l
        else:L=check(H)
    else:L,_=relation(H)
    assert H<=12 and 12+L<n-12
    rim={(i,j) for i,j in product(range(n),repeat=2) if min(i,j,n-1-i,n-1-j)<H or min(abs(2*i+1-n),abs(2*j+1-n))<cross}
    def nbr(u,d):return u[0]+DIR[d][0],u[1]+DIR[d][1]
    edges=[(u,nbr(u,d),d) for u in sorted(rim) for d in (0,1) if nbr(u,d) in rim]
    data=tables(n);typ,patch,star=data
    def emit(f,bit,flags,arc,sheet):
        # Also enforce edge orientation, outdegree and the two-sheet
        # condition on the INNER fringe, where a full star is unavailable.
        for u in sorted(rim):
            ds=[d for d in range(4) if nbr(u,d) in rim]
            for a,b in combinations(ds,2):f.append([-arc(*u,a),-arc(*u,b)])
            for d in ds:
                v=nbr(u,d);a=arc(*u,d);b=arc(*v,(d+2)%4)
                if d<2:
                    f.extend([[-a,-b],[-bit(*u),a,b],[-bit(*v),a,b],
                              [-a,bit(*u),bit(*v)],[-b,bit(*u),bit(*v)]])
                for e in range(4):
                    if e==(d+2)%4 or nbr(v,e) not in rim:continue
                    s=sheet(*u);t=sheet(*v)*(-1 if abs(d-e)==3 else 1)
                    f.extend([[-a,-arc(*v,e),-s,t],[-a,-arc(*v,e),s,-t]])
        # Cache the independently checked decision for each rooted frame.
        tested={};counts=Counter()
        def verify(model,marks):
            X={u for u in rim if bit(*u) in model}
            assert all((u in X)==bool(m) for u,m in marks.items())
            par={u:u for u in rim}
            def rt(x):
                while par[x]!=x:x=par[x]
                return x
            out={};qpos=[]
            for u,v,d in edges:
                dirs=[(u,d),(v,(d+2)%4)]
                arrows=[(z,e) for z,e in dirs if arc(*z,e) in model]
                assert len(arrows)==int(u in X or v in X)
                if arrows:
                    z,e=arrows[0];assert z not in out;out[z]=e
                    a,b=rt(u),rt(v);assert a!=b;par[a]=b
            for u in rim:
                i,j=u;ds=tuple(d for d in range(4) if all(0<=x<n for x in nbr(u,d)))
                if all(nbr(u,d) in rim for d in ds):
                    m=int(u in X)+sum((nbr(u,d) in X)<<(k+1) for k,d in enumerate(ds))
                    e=out.get(u,-1);q=star(typ(0,*u),ds,e,u==(0,0),len(ds)==2)[m]
                    if q:
                        assert e in ds and len(ds)==3 and q==72
                        a,b=nbr(u,e);assert min(a,b,n-1-a,n-1-b)==1
                        qpos.append(u)
                square=[(i+a,j+b) for a,b in product(range(3),repeat=2)]
                if all(z in rim for z in square):
                    assert patch(typ(1,*u))[sum((z in X)<<k for k,z in enumerate(square))]==0
            assert len(qpos)==1
            return out
        if shared:
            # Four rotated copies of the complete single-root annulus CNF;
            # identify mark variables only. Arrows, charges and sheet
            # variables belong to the respective orientation.
            old=f.clauses[:];top=f.nv;maps=[list(range(top+1))]
            for g in range(1,4):
                off=f.nv;ids=[0]+[off+j for j in range(1,top+1)]
                for u in rim:ids[bit(*u)]=bit(*trans(*u,n,g))
                f.extend(([ids[z] if z>0 else -ids[-z] for z in c] for c in old));maps.append(ids)
            del old
            codes=('0011','0013','0031','0033','0112','0132','0211','0213','0231','0312')
            if connector:
                from .rim_connector import install,replay
                path_edges=edges
                if cross:
                    core={u for u in rim if all(nbr(u,d) in rim or not all(0<=x<n for x in nbr(u,d)) for d in range(4))}
                    if radius==2:
                        core={u for u in core if all((i,j) in rim for i in range(max(0,u[0]-2),min(n,u[0]+3))
                                                     for j in range(max(0,u[1]-2),min(n,u[1]+3)))}
                    path_edges=[(u,v,d) for u,v,d in edges if u in core and v in core]
                sels,selected=install(f,bit,path_edges,n,{c:frame(n,tuple(map(int,c))) for c in codes})
            with Solver(name='cadical195',bootstrap_with=f.clauses) as solver:
                for code in codes:
                    word=tuple(map(int,code))
                    marks=frame(n,word);units=[bit(*u) if m else -bit(*u) for u,m in marks.items()]
                    if connector:units.append(sels[code])
                    ok=solver.solve(assumptions=units)
                    if ok:
                        model=set(solver.get_model())
                        arrows=[]
                        for g,ids in enumerate(maps):
                            view={j for j in range(1,top+1) if ids[j] in model}
                            out=verify(view,frame(n,rotate(word,(-g)%4)))
                            if connector:arrows.append((trans(0,0,n,g),{trans(*u,n,g):(e+g)%4 for u,e in out.items()}))
                        if connector:print('  path endpoints, length, signed turns, depth',replay(model,selected,marks,n,arrows),flush=True)
                    else:
                        fn=Path(f'target/shared_rim_{H}_cross{cross}.cnf');pr=fn.with_suffix('.drat')
                        # Stream the assumptions instead of copying four CNFs.
                        with fn.open('w') as out:
                            print('p cnf',f.nv,len(f.clauses)+len(units),file=out)
                            for c in f.clauses:print(*c,0,file=out)
                            for z in units:print(z,0,file=out)
                        assert subprocess.run(['target/cadical/build/cadical',str(fn),str(pr)],capture_output=True).returncode==20
                        res=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True)
                        assert res.returncode==0 and b's VERIFIED' in res.stdout
                    counts[ok]+=1;print(code,'shared marks verified' if ok else 'shared marks UNSAT, s VERIFIED',flush=True)
            print('shared survivors',counts[True],'additional exclusions',counts[False],flush=True)
            return
        with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
            for w in product(range(4),repeat=4):
                if sum(x in (0,2) for x in w)!=2 or w!=min(rotate(w,g) for g in range(8)):continue
                ok=True
                for root in range(4):
                    v=rotate(w,(-root)%4)
                    if v not in tested:
                        marks=frame(n,v);units=[bit(*u) if m else -bit(*u) for u,m in sorted(marks.items())]
                        val=s.solve(assumptions=units)
                        if val:verify(set(s.get_model()),marks)
                        else:
                            fn=Path('target/joint_rim_unsat.cnf');pr=fn.with_suffix('.drat')
                            fixed=f.copy();fixed.extend([[z] for z in units]);fixed.to_file(str(fn))
                            assert subprocess.run(['target/cadical/build/cadical',str(fn),str(pr)],capture_output=True).returncode==20
                            res=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True)
                            assert res.returncode==0 and b's VERIFIED' in res.stdout
                        tested[v]=val
                    if not tested[v]:print('  root',root,'UNSAT, s VERIFIED',flush=True)
                    ok &= tested[v]
                counts[ok]+=1
                print(''.join(map(str,w)), 'all roots feasible' if ok else 'excluded',flush=True)
        print('joint classes surviving',counts[True],'excluded',counts[False],'distinct rooted tests',len(tested),flush=True)
    window(n,'rim',H,data,exit_only=True,emit_graph=emit,cross=cross)
if __name__=='__main__':
    import sys
    test(int(sys.argv[1]),'--shared' in sys.argv or '--connector' in sys.argv,'--connector' in sys.argv,int(next((z[8:] for z in sys.argv if z.startswith('--cross=')),0)))
