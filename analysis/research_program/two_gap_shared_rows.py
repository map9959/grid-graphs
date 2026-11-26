"""Tie global tile-row activation in the north exit and corner projections."""
import sys,subprocess
from pathlib import Path
from .two_gap_exit_box import test
from .defect_window import table

def run(which,sec):
    assert '--axis=1' in sys.argv and which in ('flat','left','right')
    large='--core413' in sys.argv
    n=next((int(s[7:]) for s in sys.argv if s.startswith('--side=')),329);T=table(n)
    # The near case contains all ordinary exits within 104 of that end.
    # In the flat case both closed projections of the north ends are
    # clean (they contain no charged star). The far phase is fixed mod 3.
    specs={
        'flat':[(104,74,164,'left',[164]),(104,74,164,'right',[164]),(87,65,164,'flat',[164])],
        'left':[(150,81,53,'left',list(range(5,105,3))),(104,74,53,'right',[53])],
        'right':[(104,74,275,'left',[275]),(150,81,275,'right',list(range(224,324,3)))]}[which]
    tracks='--tracks' in sys.argv
    reroot='--reroot' in sys.argv
    if large:
        assert n==623 and which=='flat' and not tracks and not reroot
        specs=[(300,99,311,'left',[311]),(300,99,311,'right',[311]),(285,99,311,'flat',[311])]
    dest=Path(f'target/two_gap_rowlink_{which}'+('_core413' if large else '')+('_reroot' if reroot else '')+('_tracks' if tracks else '')+('_lengths' if '--lengths' in sys.argv else '')+next(('_min'+s[6:] for s in sys.argv if s.startswith('--min=')),'')+next(('_L'+s[8:].replace(',','_') for s in sys.argv if s.startswith('--fixed=')),'')+'.cnf');nv=max(200,1+len(range(14,n-14,3)));count=0;marks=[]
    with dest.open('wb') as fd:
        fd.write(b' '*63+b'\n')
        def append(c):
            nonlocal count
            fd.write((' '.join(map(str,c))+' 0\n').encode());count+=1
        def merge(f,axis,flags,bit,dom,ds,charged):
            nonlocal nv,count
            ids=[nv+z for z in range(f.nv+1)]
            for z,i in flags.items():ids[z]=1+(i-14)//3
            if reroot and len(marks)>=3:
                for p in dom:ids[bit(*p)]=marks[2][p]
            marks.append({p:ids[bit(*p)] for p in dom})
            nv+=f.nv
            for cl in f.clauses:
                fd.write((' '.join(str(ids[abs(v)] if v>0 else -ids[-v]) for v in cl)+' 0\n').encode())
            count+=len(f.clauses)
        for w,h,d,edge,ds in specs:test(w,h,d,edge,sec,merge,ds,T)
        if reroot:
            assert which=='flat'
            for heading in (1,-1):test(87,65,164,'flat',sec,merge,[164],T,heading)
        if tracks:
            assert which=='flat'
            from .two_gap_row_tracks import install
            def fresh():
                nonlocal nv
                nv+=1;return nv
            install(marks,lambda i:1+(i-14)//3,fresh,append)
        fd.seek(0);fd.write(f'p cnf {nv} {count}'.encode().ljust(63)+b'\n')
    pr=dest.with_suffix('.drat')
    if sec==0:
        assert 's SATISFIABLE' in dest.with_suffix('.log').read_text();rc=10
    else:
        with dest.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(dest),str(pr)],stdout=fd).returncode
    if rc==20:
        data=subprocess.run(['target/drat-trim/drat-trim',str(dest),str(pr)],check=True,capture_output=True).stdout
        assert b's VERIFIED' in data;dest.with_suffix('.check').write_bytes(data);print(which,'s VERIFIED',flush=True)
    elif rc==10:
        model={int(w) for line in dest.with_suffix('.log').open() if line.startswith('v ') for w in line.split()[1:]}
        assert not any(-w in model for w in model if w>0)
        if len(model)-1<nv:
            from pysat.solvers import Solver
            with Solver(name='cadical195') as solver,dest.open() as fd:
                fd.readline()
                for line in fd:
                    c=list(map(int,line.split()[:-1]))
                    if not any(x in model for x in c):solver.add_clause([v for v in c if -v not in model])
                assert solver.solve();model.update(v for v in solver.get_model() if -v not in model)
        with dest.open() as fd:
            fd.readline()
            for line in fd:assert any(int(x) in model for x in line.split()[:-1])
        print(which,'joint row projection SAT; checked',count,'clauses')
        dest.with_suffix('.bits').write_bytes(bytes(sum(1<<(j%8) for j in range(i,min(nv,i+8)) if j+1 in model) for i in range(0,nv,8)))
    else:assert rc==0;print(which,'UNKNOWN')
if __name__=='__main__':run(sys.argv[1],int(sys.argv[2]))
