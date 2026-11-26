"""Search the certified side-109 survivor union with compatible corner splits."""
import hashlib,json,shutil,subprocess,sys
from pathlib import Path
from . import sector_eighth_split as eighth, sector_third_split as sat
from .square_dual_physical import DIR,trans
from .extend_forest_28 import verify

dest=Path('target/sector_survivor_tree');n=109
def survivors():
    cs=eighth.cases();dead=set()
    assert hashlib.sha256(eighth.manifest.read_bytes()).hexdigest()=='e059b0a3b6343adecf546430cb63106fe80e9560f9b8c3e607c87a60459c96d8'
    for _,m in json.loads(eighth.manifest.read_text()).values():
        ks={k for k in cs if m.get(k.rsplit('_',1)[0],0)&(1<<int(k.rsplit('_',1)[1]))}
        assert len(ks)==sum(v.bit_count() for v in m.values()) and ks.isdisjoint(dead)
        dead.update(ks)
    live={k:c for k,c in cs.items() if k not in dead}
    assert len(live)==247 and sum(len(sat.orbit(c)) for c in live.values())==1912
    return live

def owner_maps():
    # Check the actual per-site owner disjunctions in the matching source;
    # no assumptions about auxiliary IDs from the score-budget encoding.
    own={};v=551142
    for i in range(n):
        for j in range(n):
            if (i,j)==(0,0):continue
            for d,(a,b) in enumerate(DIR):
                if 0<=i+a<n and 0<=j+b<n:v+=1;own[i,j,d]=v
    assert v==644884-4*(n-1)**2
    expected={b' '.join(str(own[i,j,d]).encode() for d in range(4) if (i,j,d) in own)+b' 0\n'
              for i in range(n) for j in range(n) if i or j}
    with Path('target/sector109_4078_matching.cnf').open('rb') as s:
        assert s.readline().split()==[b'p',b'cnf',b'644884',b'4370519']
        for line in s:expected.discard(line)
    assert not expected
    return [{(*trans(i,j,n,g),(d+g)%4):v+g*644884 for (i,j,d),v in own.items()} for g in range(4)]

def split_clauses(owners,switch):
    for i in range(n):
        for j in range(n):
            for d in (0,1):
                a,b=DIR[d]
                if i+a>=n or j+b>=n:continue
                ids=[o.get((i,j,d)) for o in owners]
                for mask,guard in ((5,0),(10,0),(3,switch),(12,switch),(6,-switch),(9,-switch)):
                    if any(v is None and mask>>g&1 for g,v in enumerate(ids)):continue
                    yield ([guard] if guard else [])+[(-v if mask>>g&1 else v) for g,v in enumerate(ids) if v is not None]

def build(live):
    with sat.joint.src.open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==sat.digest
    owners=owner_maps();switch=2532881
    extra=list(split_clauses(owners,switch))
    keys=list(live);ids=list(range(switch+1,switch+1+len(keys)))
    extra.append(ids)
    for z,k in zip(ids,keys):extra.extend([[-z,x] for x in live[k]])
    # Propagate common literals without requiring the solver to pick a selector.
    extra.extend([[x] for x in sorted(set.intersection(*(set(c) for c in live.values())))])
    with (dest/'all.cnf').open('wb') as out,sat.joint.src.open('rb') as inp:
        _,_,_,nc=inp.readline().split()
        out.write(f'p cnf {ids[-1]} {int(nc)+len(extra)}\n'.encode());shutil.copyfileobj(inp,out)
        for c in extra:out.write((' '.join(map(str,c))+' 0\n').encode())
    print('joint survivor disjunction',len(keys),'classes; added clauses',len(extra),flush=True)

def decision(live,secs):
    cnf=dest/'all.cnf';proof=dest/'all.drat'
    with (dest/'all.log').open('w') as out:
        r=subprocess.run(['target/cadical/build/cadical','-t',str(secs),str(cnf),str(proof)],stdout=out)
    if r.returncode==0:print('joint search UNKNOWN',flush=True);return
    if r.returncode==20:
        ck=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(proof)],capture_output=True)
        assert ck.returncode==0 and b's VERIFIED' in ck.stdout
        (dest/'all.check').write_bytes(ck.stdout);print('s VERIFIED all 247',flush=True)
    else:
        assert r.returncode==10
        model={int(x) for l in (dest/'all.log').read_text().splitlines() if l.startswith('v ') for x in l[2:].split()}
        rows=[''.join('#' if 1+i*n+j in model else '.' for j in range(n)) for i in range(n)]
        sc=verify(rows);assert sc[0]==sc[-1]==4078
        (dest/'all.forest').write_text('\n'.join(rows)+'\n');print('verified',sc)

def selected(live,limit):
    from pysat.solvers import Solver
    results={}
    with Solver(name='cadical195') as s,(dest/'all.cnf').open('rb') as inp:
        inp.readline()
        for l in inp:s.add_clause(list(map(int,l.split()[:-1])))
        for idx,(k,c) in enumerate(live.items(),2532882):
            s.conf_budget(limit);v=s.solve_limited(assumptions=[idx,*c])
            results[k]={True:'SAT',False:'UNSAT',None:'UNKNOWN'}[v]
            if v:
                m=set(s.get_model());rows=[''.join('#' if 1+i*n+j in m else '.' for j in range(n)) for i in range(n)]
                sc=verify(rows);assert sc[0]==sc[-1]==4078
                (dest/'selected.forest').write_text('\n'.join(rows)+'\n');print('verified',sc)
            print(k,results[k],flush=True)
            (dest/'selected.json').write_text(json.dumps(results,indent=2))

def certificate(live,keys,secs):
    ids=[i for i,k in enumerate(live,2532882) if k in keys]
    assert len(ids)==len(set(keys))==len(keys) and ids
    path=dest/('selected_'+str(len(ids)))
    with (dest/'all.cnf').open('rb') as inp,path.with_suffix('.cnf').open('wb') as out:
        _,_,nv,nc=inp.readline().split()
        out.write(f'p cnf {int(nv)} {int(nc)+1}\n'.encode());shutil.copyfileobj(inp,out)
        out.write((' '.join(map(str,ids))+' 0\n').encode())
    fn=str(path.with_suffix('.cnf'));pr=str(path.with_suffix('.drat'))
    r=subprocess.run(['target/cadical/build/cadical','-t',str(secs),fn,pr],capture_output=True)
    if r.returncode==0:print('certificate run UNKNOWN');return False
    assert r.returncode==20
    r=subprocess.run(['target/drat-trim/drat-trim',fn,pr],capture_output=True)
    assert r.returncode==0 and b's VERIFIED' in r.stdout;path.with_suffix('.check').write_bytes(r.stdout)
    path.with_suffix('.json').write_text(json.dumps(keys));print('s VERIFIED',len(ids),'classes',flush=True)
    return True

def certified(live,secs=None):
    dead=set()
    for ncase,(h,keys) in json.loads(Path(__file__).with_name('sector_survivor_proofs.json').read_text()).items():
        assert len(set(keys))==len(keys)==int(ncase) and dead.isdisjoint(keys) and set(keys)<=live.keys()
        if secs is not None:assert certificate(live,keys,secs)
        p=dest/f'selected_{ncase}'
        with p.with_suffix('.cnf').open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==h
        assert b's VERIFIED' in p.with_suffix('.check').read_bytes() and keys==json.loads(p.with_suffix('.json').read_text())
        dead.update(keys)
    return dead

def hinted(live,limit):
    from pysat.solvers import Solver
    from .comb_cap_transfer import construct
    dead=certified(live);rows=construct(n,4);sc=verify(rows);assert sc[0]==sc[-1]==4077
    with Solver(name='cadical195') as s,(dest/'all.cnf').open('rb') as inp:
        inp.readline()
        for l in inp:s.add_clause(list(map(int,l.split()[:-1])))
        for i,k in enumerate(live,2532882):
            if k in dead:s.add_clause([-i])
        s.set_phases([(1+i*n+j)*(1 if rows[i][j]=='#' else -1) for i in range(n) for j in range(n)])
        s.conf_budget(limit);v=s.solve_limited()
        print('4077 hint, remaining union:',v,flush=True)
        if v:
            m=set(s.get_model());rows=[''.join('#' if 1+i*n+j in m else '.' for j in range(n)) for i in range(n)]
            sc=verify(rows);assert sc[0]==sc[-1]==4078
            (dest/'hint.forest').write_text('\n'.join(rows)+'\n');print('verified',sc)
        elif v is False:assert certificate(live,[k for k in live if k not in dead],7200)
if __name__=='__main__':
    dest.mkdir(exist_ok=True);live=survivors()
    if sys.argv[1]=='build':build(live)
    elif sys.argv[1]=='selected':selected(live,int(sys.argv[2]))
    elif sys.argv[1]=='hint':hinted(live,int(sys.argv[2]))
    elif sys.argv[1] in ('certified','audit'):
        dead=certified(live,int(sys.argv[2]) if sys.argv[1]=='certified' else None)
        print('verified exclusions',len(dead),'remaining',len(live)-len(dead))
    elif sys.argv[1]=='prove':
        res=json.loads((dest/'selected.json').read_text());assert set(res)==live.keys()
        certificate(live,[k for k in live if res[k]=='UNSAT'],int(sys.argv[2]))
    else:decision(live,int(sys.argv[1]))
