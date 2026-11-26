"""Project the depth-3 east signature/site pairs to one rerooted corner."""
from pathlib import Path
import json,subprocess,hashlib,sys
from pysat.formula import CNF
from pysat.solvers import Solver
from .offrail103_d3_sites import OUT,N,build

def run():
    n=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--side=')),N)
    assert n in (103,112)
    label='local' if n==103 else f'local{n}'
    remote='--remote-root' in sys.argv
    if remote:label+='_remote'
    _,_,_,_,cases=build('south')
    sigs=sorted({k.split('-')[1].split('@')[0] for k in cases})
    masks=sorted({k.split('@')[1] for k in cases})
    f=CNF(from_file=f"target/offrail{n}_crop_3_7_size30_sites{'-'.join(masks)}"+('_remote' if remote else '')+'.cnf')
    row=lambda r:n-1-r if remote else r
    sels=f.clauses[-1];assert len(sels)==len(masks)
    for i,(z,m) in enumerate(zip(sels,masks)):
        for b,cl in enumerate(f.clauses[-(1+6*len(sels))+6*i:][:6]):
            x=1+n*row(7+b//3)+6+b%3
            assert cl==[-z,x if int(m,16)>>b&1 else -x]
    groups=[]
    for t in range(6):
        vs=[1+n*row(i)+j for i in (3*t+1,3*t+2) if i<=16 for j in (6,7,8)]
        g=f.nv+1;groups.append(g);f.append([-g,*vs]);f.extend([[-v,g] for v in vs])
    cases={}
    for s in sigs:
        z=f.nv+1
        for i,g in enumerate(groups):f.append([-z,g if str(i) in s else -g])
        for m,x in zip(masks,sels):
            v=f.nv+1;cases[s+'@'+m]=v;f.extend([[-v,x],[-v,z]])
    if '--replay' in sys.argv:
        rec=json.loads((OUT/f'{label}.json').read_text());assert cases.keys()==rec.keys()
        f.append([v for k,v in cases.items() if rec[k]=='VERIFIED'])
        p=OUT/f'{label}_union.cnf';tmp=OUT/f'{label}_audit.cnf';f.to_file(str(tmp))
        assert hashlib.sha256(tmp.read_bytes()).digest()==hashlib.sha256(p.read_bytes()).digest();tmp.unlink()
        data=subprocess.run(['target/drat-trim/drat-trim',str(p),str(p.with_suffix('.drat'))],check=True,capture_output=True).stdout
        assert b's VERIFIED' in data;print(data.decode().splitlines()[-2:]);return
    log={};dead=[]
    with Solver(name='cadical195',bootstrap_with=f.clauses) as sol:
        for k,v in cases.items():
            sol.conf_budget(4500);r=sol.solve_limited(assumptions=[v])
            if r is False:dead.append(v)
            log[k]='pending' if r is False else 'UNKNOWN' if r is None else 'crop SAT'
    if dead:
        p=OUT/f'{label}_union.cnf';pr=p.with_suffix('.drat')
        f.append(dead);f.to_file(str(p))
        with p.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t','90',str(p),str(pr)],stdout=fd).returncode
        if rc==20:
            data=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],check=True,capture_output=True).stdout
            assert b's VERIFIED' in data;p.with_suffix('.check').write_bytes(data)
            for k,v in cases.items():
                if v in dead:log[k]='VERIFIED'
            print(hashlib.sha256(p.read_bytes()).hexdigest(),[l for l in data.decode().splitlines() if 'resolution steps' in l])
    (OUT/f'{label}.json').write_text(json.dumps(log,indent=1)+'\n')
    from collections import Counter
    print(len(cases),Counter(log.values()))
if __name__=='__main__':run()
