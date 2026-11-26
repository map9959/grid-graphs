"""Reconstruct a corner sweep, check the labelled disjunction, replay its DRAT."""
import hashlib,json,shutil,subprocess,sys
from pathlib import Path
from .offrail103_pair_sweep import BASE,build,site_cases

def audit(tag,budget):
    exact='--exact35' in sys.argv
    joint='--joint35' in sys.argv
    two8='--two8' in sys.argv
    dest=Path('target/offrail103_two8' if two8 else 'target/offrail103_joint35' if joint else 'target/offrail103_exact35' if exact else 'target/offrail103_pair_sweep')
    sites='--sites' in sys.argv
    if sites:dest=Path('target/offrail103_sites')
    records=json.loads((dest/f'{tag}_{budget}.json').read_text())
    base,f,cases=build(tag!='board',tag in ('crop2','strip','collar'),exact,joint,two8)
    if sites:cases=site_cases(f,cases,tag=='collar')
    if tag in ('crop2','strip','collar') and two8 and not sites:
        old=json.loads((dest/'crop_1600.json').read_text())
        cases={k:v for k,v in cases.items() if old[f'{k[0]}:{k[1]}']!='VERIFIED UNSAT'}
        if tag in ('strip','collar'):
            prev=[json.loads((dest/p).read_text()) for p in ['board_500.json','crop2_5000.json']+(['strip_10000.json'] if tag=='collar' else [])]
            cases={k:v for k,v in cases.items() if all(r.get(f'{k[0]}:{k[1]}')!='VERIFIED UNSAT' for r in prev)}
    if tag=='crop2' and not (exact or joint or two8):
        old=json.loads((dest/'crop_1200.json').read_text())
        cases={k:v for k,v in cases.items() if old[f'{k[0]}:{k[1]}']!='VERIFIED UNSAT'}
    assert {f'{d}:{p}' for d,p in cases}==set(records)
    dead=[v for (d,p),v in cases.items() if records[f'{d}:{p}']=='VERIFIED UNSAT']
    assert dead
    f.append(dead);tmp=dest/f'{tag}_audit.cnf'
    if base is not None:base.extend(f.clauses);base.to_file(str(tmp))
    else:
        with BASE.open('rb') as src,tmp.open('wb') as fd:
            nc=int(src.readline().split()[3])
            fd.write(f'p cnf {f.nv} {nc+len(f.clauses)}\n'.encode());shutil.copyfileobj(src,fd)
            for c in f.clauses:fd.write((' '.join(map(str,c))+' 0\n').encode())
    def digest(p):
        with p.open('rb') as fd:return hashlib.file_digest(fd,'sha256').hexdigest()
    orig=dest/f'{tag}_union.cnf'
    assert digest(tmp)==digest(orig);tmp.unlink()
    result=subprocess.run(['target/drat-trim/drat-trim',str(orig),str(orig.with_suffix('.drat'))],check=True,capture_output=True)
    assert b's VERIFIED' in result.stdout
    print(tag,'cases',len(records),'excluded',len(dead),'CNF',digest(orig),flush=True)
    print('\n'.join(l for l in result.stdout.decode().splitlines() if 'resolution steps' in l or 's VERIFIED' in l))
if __name__=='__main__':audit(sys.argv[1],int(sys.argv[2]))
