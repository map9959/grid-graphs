"""Exhaustive surviving orbit queries on the joint four-root score CNF."""
from .sector_perimeter_split import (n,groups,cube,continuation,certified,rotated_units,
                                     verify,Path,json,subprocess,shutil,sys,coverage)
dest=Path('target/four_root_sector');src=dest/'base.cnf'

def cases():
    gs=groups()
    def key(c):return min(tuple(sorted(rotated_units(c,g))) for g in range(8))
    banned={key(c) for c in certified(gs)}
    w='011101010101';banned.add(key(cube(w)+continuation(w,13)))
    seen=set();res={}
    for w in sorted(gs):
        for m in range(16):
            c=cube(w)+continuation(w,m);k=key(c)
            if k not in banned and k not in seen:
                seen.add(k);res[w+'_'+str(m)]=c
    assert len(res)==22
    return res

def solve(cs,limit):
    from pysat.solvers import Solver
    out=dest/'results.json'
    results=json.loads(out.read_text()) if '--resume' in sys.argv else {}
    with Solver(name='cadical195') as s,src.open('rb') as inp:
        assert inp.readline().split()==[b'p',b'cnf',b'2532880',b'17482076']
        for line in inp:s.add_clause(list(map(int,line.split()[:-1])))
        for name,c in cs.items():
            if results.get(name) in ('UNSAT','SAT'):continue
            s.conf_budget(limit);v=s.solve_limited(assumptions=c)
            results[name]={False:'UNSAT',True:'SAT',None:'UNKNOWN'}[v]
            if v:
                m=set(s.get_model());rows=[''.join('#' if i*n+j+1 in m else '.' for j in range(n)) for i in range(n)]
                score=verify(rows);assert score[0]==score[-1]==4078
                (dest/(name+'.forest')).write_text('\n'.join(rows)+'\n')
                print('verified forest',score,flush=True)
            print(name,results[name],flush=True)
            out.write_text(json.dumps(results,indent=2))

def prove(cs,seconds):
    if '--certified' in sys.argv:
        neg=[cs['011101010101_'+str(m)] for m in (7,11)]
    else:
        result=json.loads((dest/'results.json').read_text());assert set(result)==set(cs)
        neg=[cs[k] for k,v in result.items() if v=='UNSAT']
    if not neg:return
    prefix=dest/f'cases_{len(neg)}'
    with src.open('rb') as inp,prefix.with_suffix('.cnf').open('wb') as out:
        _,_,nv,nc=inp.readline().split();nv=int(nv)
        selectors=list(range(nv+1,nv+1+len(neg)))
        extra=[selectors]+[[-z,l] for z,c in zip(selectors,neg) for l in c]
        out.write(f'p cnf {selectors[-1]} {int(nc)+len(extra)}\n'.encode());shutil.copyfileobj(inp,out)
        for c in extra:out.write((' '.join(map(str,c))+' 0\n').encode())
    fn=str(prefix.with_suffix('.cnf'));pr=str(prefix.with_suffix('.drat'))
    r=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),fn,pr],capture_output=True)
    assert r.returncode==20,r.stdout[-200:]
    r=subprocess.run(['target/drat-trim/drat-trim',fn,pr],capture_output=True)
    assert r.returncode==0 and b's VERIFIED' in r.stdout
    prefix.with_suffix('.check').write_bytes(r.stdout)
    print('joint four-root proof: s VERIFIED for',len(neg),'classes')
if __name__=='__main__':
    coverage();cs=cases()
    if sys.argv[1]=='solve':solve(cs,int(sys.argv[2]))
    else:prove(cs,int(sys.argv[2]))
