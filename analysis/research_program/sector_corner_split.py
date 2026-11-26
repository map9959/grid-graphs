"""Exhaustive six-bit split of the physical 109 matching CNF."""
import hashlib,itertools,json,shutil,subprocess,sys
from pathlib import Path
from .extend_forest_28 import verify

src=Path('target/sector109_4078_matching.cnf')
prefix=Path('target/sector109_split')
marks=(1,109,11881,11773,2,110)  # NW NE SE SW; east and south of NW
words=list(itertools.product((0,1),repeat=len(marks)))
def cube(w):return [v if b else -v for v,b in zip(marks,w)]

def coverage():
    assert hashlib.sha256(src.read_bytes()).hexdigest()=='d73ee0c77242267b34fe466bbf45fee2f011252f38bd160609108dd7ec6539fa'
    for w in words:
        truth=set(cube(w))
        assert sum(set(cube(v))<=truth for v in words)==1
    print('coverage:',len(words),'disjoint exhaustive assignments; CNF hash checked',flush=True)

def certified_summary():
    # Complement of the checked 45-case disjunction. Fixed list makes
    # replay independent of the solver version and of incremental ordering.
    rest=('001101 001110 010101 010110 011001 011010 011101 011110 '
          '100101 100110 101001 101101 101110 110101 110110 111001 '
          '111010 111101 111110').split()
    res={''.join(map(str,w)):('UNKNOWN' if ''.join(map(str,w)) in rest else 'UNSAT') for w in words}
    assert len(rest)==19 and all(s[-2:] in ('01','10') for s in rest)
    assert not any(s[:4]=='1100' or s[:4].count('1')<2 for s in rest)
    assert {s[-2:] for s in rest if s[:4]=='1010'}=={'01'}
    return res

def search(limit):
    from pysat.solvers import Solver
    with Solver(name='cadical195') as s,src.open('rb') as inp:
        assert inp.readline().split()==[b'p',b'cnf',b'644884',b'4370519']
        for l in inp:s.add_clause(list(map(int,l.split()[:-1])))
        result=json.loads(prefix.with_suffix('.json').read_text()) if '--resume' in sys.argv else {}
        for w in words:
            label=''.join(map(str,w))
            if result.get(label) in ('SAT','UNSAT'):continue
            s.conf_budget(limit)
            status=s.solve_limited(assumptions=cube(w))
            if status:
                m=set(s.get_model());n=109
                rows=[''.join('#' if 1+i*n+j in m else '.' for j in range(n)) for i in range(n)]
                vals=verify(rows);assert vals[0]==vals[-1]==4078
                prefix.with_suffix('.forest').write_text('\n'.join(rows)+'\n');print('forest',vals)
            result[label]={True:'SAT',False:'UNSAT',None:'UNKNOWN'}[status]
            print(label,result[label],flush=True)
            if '--resume' in sys.argv:prefix.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
        prefix.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')

def check(seconds):
    res=certified_summary() if '--certified' in sys.argv else json.loads(prefix.with_suffix('.json').read_text())
    assert set(res)=={''.join(map(str,w)) for w in words}
    excluded=[w for w in words if res[''.join(map(str,w))]=='UNSAT']
    assert excluded
    if '--tag' in sys.argv:
        outprefix=prefix.with_name(prefix.name+'_'+str(len(excluded)))
    else:outprefix=prefix
    rest=[w for w in words if w not in excluded]
    clauses=[[-x for x in cube(w)] for w in rest]
    for w in words:
        assert all(set(c)&set(cube(w)) for c in clauses)==(w in excluded)
    cnf=outprefix.with_suffix('.cnf');pr=outprefix.with_suffix('.drat')
    with src.open('rb') as inp,cnf.open('wb') as out:
        _,_,nv,nc=inp.readline().split()
        out.write(b'p cnf %s %d\n'%(nv,int(nc)+len(clauses)));shutil.copyfileobj(inp,out)
        for c in clauses:out.write((' '.join(map(str,c))+' 0\n').encode())
    proc=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(cnf),str(pr)],capture_output=True)
    print('proof run',proc.returncode,proc.stdout[-100:],flush=True)
    if proc.returncode==0:raise SystemExit('combined proof run timed out; previous exclusions only')
    assert proc.returncode==20
    r=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(pr)],capture_output=True)
    assert r.returncode==0 and b's VERIFIED' in r.stdout
    outprefix.with_suffix('.check').write_bytes(r.stdout)
    print('combined exclusion s VERIFIED:',len(excluded),'cases;',len(rest),'outside this proof',flush=True)
if __name__=='__main__':
    coverage()
    if sys.argv[1]=='search':search(int(sys.argv[2]))
    else:check(int(sys.argv[2]))
