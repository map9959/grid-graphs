"""Score 3647: exact east pair (up to reflection), or both corners >=3."""
from itertools import combinations,combinations_with_replacement
from pathlib import Path
import hashlib,json,shutil,subprocess,sys
from pysat.formula import CNF
from pysat.solvers import Solver
from .offrail103_one_depth import BASE,HASH,N,band,suffix,group_cut,verify

def branches(d):
    for a,b in combinations(range(6),2):
        if (a,b)==(0,1) or d>=5 and b==2:continue
        yield f'{a}{b}'
    yield 'both3'

def build(crop,refine,exact=False,joint=False,two8=False):
    if two8:
        old=Path('target/offrail103_pair_sweep')
        verdicts=[json.loads((old/n).read_text()) for n in ('board_600.json','crop_1200.json','crop2_5000.json')]
    if joint:
        exact=True
        previous=Path('target/offrail103_exact35')
        records=[json.loads((previous/n).read_text()) for n in ('board_800.json','crop_2400.json','crop2_1500.json')]
    if crop:
        from .diagonal_score import generate
        region={(i,y) for i in range(30) for j in range(30) if i<=14 or j<=11 or (refine and max(i,j)<24) for y in (j,N-1-j)}
        if '--joined-strip' in sys.argv:
            assert two8 and refine
            region.update((i,j) for i in range(18) for j in range(N))
            if '--full-collar' in sys.argv:
                region.update((i,j) for i in range(N) for j in range(N) if min(j,N-1-j,N-1-i)<15)
        base,_=generate(N,3647,region)
        if refine:
            offset=base.nv;shared={1+N*i+j:1+N*i+N-1-j for i,j in region}
            for ls in base.clauses[:]:
                base.append([(1 if x>0 else -1)*shared.get(abs(x),offset+abs(x)) for x in ls])
        top=base.nv
    else:
        with BASE.open('rb') as fd:assert hashlib.file_digest(fd,'sha256').hexdigest()==HASH
        with BASE.open('rb') as fd:top=int(fd.readline().split()[2])
        base=None
    f=CNF();groups=list(range(top+1,top+13));top,cut=group_cut(top,'west');f.extend(cut)
    if two8:f.append([groups[2],groups[8]])
    cases={}
    for d in ((3,5) if exact else range(2,11)):
        if crop:
            c=[[-v] for v in band(0,d) if '--joined-strip' in sys.argv or min((v-1)%N,N-1-(v-1)%N)<30]
            if '--joined-strip' in sys.argv:c.extend(band(0,i) for i in range(d))
            if '--full-collar' in sys.argv:c.extend(band(s,i) for s in (1,2,3) for i in range(11))
        else:top,c=suffix(d,top)
        top+=1;z=top
        f.extend([[-z,*ls] for ls in c])
        patterns=(''.join(map(str,s)) for k in range(3,7) for s in combinations(range(6),k)) if exact else branches(d)
        if joint:
            surviving=[p for p in patterns if all(r[f'{d}:{p}']!='VERIFIED UNSAT' for r in records)]
            assert len(surviving)=={3:20,5:18}[d]
            patterns=(a+'-'+b for a,b in combinations_with_replacement(surviving,2))
        if two8:
            east=[p for p in branches(d) if p!='both3' and all(r.get(f'{d}:{p}')!='VERIFIED UNSAT' for r in verdicts)]
            patterns=(''.join(a)+'-'+b for b in east for k in range(3,7) for a in combinations('012345',k) if '2' in a or '2' in b)
        for p in patterns:
            top+=1;t=top;cases[d,p]=t;f.append([-t,z])
            if joint or two8:
                for side,mask in enumerate(p.split('-')):
                    for i,x in enumerate(groups[6*side:6*side+6]):
                        f.append([-t,x if str(i) in mask else -x])
            elif p=='both3':f.extend([[-t,*vs] for vs in combinations(groups[6:],4)])
            else:
                for i,x in enumerate(groups[6:]):
                    f.append([-t,x if str(i) in p else -x])
    return base,f,cases

def site_cases(f,cases,collar=False):
    parents=[(6,'123-23'),(6,'0123-23'),(6,'1234-23'),(8,'123-23'),(8,'0123-23')]
    sites=[1+r*N+N-1-j for r in (7,8) for j in (6,7,8)]
    assert set(sites)=={x for x in band(3,7) if (x-1)//N in (7,8)}
    result={}
    for d,p in parents:
        for mask in range(1,64):
            z=f.nv+1;f.append([-z,cases[d,p]])
            for i,x in enumerate(sites):f.append([-z,x if mask>>i&1 else -x])
            result[d,f'{p}@{mask:02x}']=z
    if collar:
        dest=Path('target/offrail103_sites')
        prev=[json.loads((dest/p).read_text()) for p in ('board_500.json','strip_1200.json')]
        return {k:v for k,v in result.items() if all(r[f'{k[0]}:{k[1]}']!='VERIFIED UNSAT' for r in prev)}
    return result

def run(crop,budget):
    refine='--refine' in sys.argv
    tag=('crop2' if refine else 'crop') if crop else 'board'
    if '--joined-strip' in sys.argv:tag='strip'
    if '--full-collar' in sys.argv:
        assert '--joined-strip' in sys.argv
        tag='collar'
    exact='--exact35' in sys.argv
    joint='--joint35' in sys.argv
    two8='--two8' in sys.argv
    out=Path('target/offrail103_two8' if two8 else 'target/offrail103_joint35' if joint else 'target/offrail103_exact35' if exact else 'target/offrail103_pair_sweep');out.mkdir(exist_ok=True)
    sites='--sites' in sys.argv
    if sites:
        assert two8
        out=Path('target/offrail103_sites');out.mkdir(exist_ok=True)
    base,f,cases=build(crop,refine,exact,joint,two8)
    assert len(cases)==(320 if two8 else 381 if joint else 84 if exact else 123)
    if sites:cases=site_cases(f,cases,tag=='collar')
    if refine and two8 and not sites:
        old=json.loads((out/'crop_1600.json').read_text())
        assert b's VERIFIED' in (out/'crop_union.check').read_bytes()
        cases={k:v for k,v in cases.items() if old[f'{k[0]}:{k[1]}']!='VERIFIED UNSAT'}
        if tag in ('strip','collar'):
            prev=[json.loads((out/p).read_text()) for p in ['board_500.json','crop2_5000.json']+(['strip_10000.json'] if tag=='collar' else [])]
            cases={k:v for k,v in cases.items() if all(r.get(f'{k[0]}:{k[1]}')!='VERIFIED UNSAT' for r in prev)}
    if refine and not (exact or joint or two8):
        old=json.loads((out/'crop_1200.json').read_text())
        assert (out/'crop_union.check').read_bytes().find(b's VERIFIED')>=0
        cases={k:v for k,v in cases.items() if old[f'{k[0]}:{k[1]}']!='VERIFIED UNSAT'}
    dead=[];log={}
    with Solver(name='cadical195') as solver:
        if crop:solver.append_formula(base.clauses)
        else:
            with BASE.open('rb') as fd:
                fd.readline()
                for line in fd:solver.add_clause(list(map(int,line.split()[:-1])))
        solver.append_formula(f.clauses)
        for (d,p),v in cases.items():
            solver.conf_budget(budget);res=solver.solve_limited(assumptions=[v])
            k=f'{d}:{p}'
            if res is False:dead.append(v);log[k]='pending proof'
            elif res is None:log[k]='UNKNOWN'
            elif crop:log[k]='crop SAT'
            else:
                m=set(solver.get_model())
                rows=[''.join('#' if i*N+j+1 in m else '.' for j in range(N)) for i in range(N)]
                witness=verify(rows);assert witness[-1]>=3647
                (out/f'tree_{d}_{p}.txt').write_text('\n'.join(rows)+'\n');log[k]=str(witness)
            if p=='both3':print(tag,d,'tested',len(log),'provisional UNSAT',len(dead),flush=True)
    if dead:
        f.append(dead);path=out/f'{tag}_union.cnf';pr=path.with_suffix('.drat')
        if crop:
            base.extend(f.clauses);base.to_file(str(path))
        else:
            with BASE.open('rb') as src,path.open('wb') as fd:
                nc=int(src.readline().split()[3]);fd.write(f'p cnf {f.nv} {nc+len(f.clauses)}\n'.encode());shutil.copyfileobj(src,fd)
                for c in f.clauses:fd.write((' '.join(map(str,c))+' 0\n').encode())
        with path.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t','180',str(path),str(pr)],stdout=fd).returncode
        if rc==20:
            data=subprocess.run(['target/drat-trim/drat-trim',str(path),str(pr)],capture_output=True,check=True).stdout
            assert b's VERIFIED' in data;path.with_suffix('.check').write_bytes(data)
            log={k:('VERIFIED UNSAT' if v=='pending proof' else v) for k,v in log.items()}
        else:print('joint proof unavailable',rc)
    (out/f'{tag}_{budget}.json').write_text(json.dumps(log,indent=1)+'\n')
    from collections import Counter
    print(tag,Counter(log.values()),flush=True)
if __name__=='__main__':run(sys.argv[1]=='crop',int(sys.argv[2]))
