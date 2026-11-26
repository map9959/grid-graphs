"""South-rooted necessary collar at first empty depth 3 or 5."""
from pathlib import Path
from collections import Counter
import hashlib,json,subprocess,sys
from pysat.solvers import Solver
from .diagonal_score import generate
from .offrail103_one_depth import N,band
from .offrail103_joint_summary import report

def test(d,budget):
    pairs=report()[d];assert len(pairs)=={3:155,5:162}[d]
    out=Path('target/offrail103_joint_south');out.mkdir(exist_ok=True)
    region={(i,j) for i in range(N) for j in range(N) if min(i,j,N-1-j)<15 or i>=N-21}
    f,X=generate(N,3647,region)
    def lit(v):
        r,c=divmod(v-1,N);return X[(N-1-r)*N+c]
    for t in range(d):f.append([lit(v) for v in band(0,t)])
    for v in band(0,d):f.append([-lit(v)])
    for side in (1,2,3):
        for t in range(11):f.append([lit(v) for v in band(side,t)])
    groups=[]
    for side in (1,3):
        for t in range(6):
            vs=[lit(v) for v in band(side,7) if (v-1)//N<=16 and (v-1)//N//3==t]
            g=f.nv+1;f.append([-g,*vs]);f.extend([[-v,g] for v in vs]);groups.append(g)
    signature=next((x.split('=')[1] for x in sys.argv if x.startswith('--one-corner=')),None)
    if signature is not None:
        # No restriction on the other signature beyond the proven
        # three-group minimum and the shared group-2 requirement.
        from itertools import combinations
        if signature.startswith('omit'):
            f.append([-groups[int(signature[4:])]])
            for vs in combinations(groups[:6],4):f.append(list(vs))
        else:
            for mask,g in enumerate(groups[:6]):f.append([g if str(mask) in signature else -g])
        for vs in combinations(groups[6:],4):f.append(list(vs))
        f.append([groups[2],groups[8]])
        stem=out/f'd{d}_only_{signature}';p=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
        f.to_file(str(p))
        with stem.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t',str(budget),str(p),str(pr)],stdout=fd).returncode
        if rc==20:
            data=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],check=True,capture_output=True).stdout
            assert b's VERIFIED' in data;stem.with_suffix('.check').write_bytes(data)
        print('single signature',d,signature,{0:'UNKNOWN',20:'s VERIFIED',10:'crop SAT'}[rc]);return
    selectors={}
    for a,b in pairs:
        z=f.nv+1;selectors[a+'-'+b]=z
        for i,g in enumerate(groups):f.append([-z,g if str(i%6) in (a,b)[i//6] else -g])
    status={};dead=[]
    with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
        for k,z in selectors.items():
            s.conf_budget(budget);r=s.solve_limited(assumptions=[z])
            status[k]='pending' if r is False else 'UNKNOWN' if r is None else 'crop SAT'
            if r is False:dead.append(k)
    def certify(keys,tag):
        if not keys:return
        stem=out/f'd{d}_{tag}';p=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
        f.append([selectors[k] for k in keys]);f.to_file(str(p));f.clauses.pop()
        with stem.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t','120',str(p),str(pr)],stdout=fd).returncode
        if rc==20:
            data=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],capture_output=True,check=True).stdout
            assert b's VERIFIED' in data;stem.with_suffix('.check').write_bytes(data)
            for k in keys:status[k]='VERIFIED '+tag
            with p.open('rb') as fd:h=hashlib.file_digest(fd,'sha256').hexdigest()
            print(d,tag,len(keys),h,[s for s in data.decode().splitlines() if 'resolution steps' in s],flush=True)
        elif rc==0 and len(keys)>12:
            pr.unlink(missing_ok=True);p.unlink()
            mid=len(keys)//2;certify(keys[:mid],tag+'a');certify(keys[mid:],tag+'b')
        else:assert rc==0
    certify(dead,'union')
    (out/f'd{d}.json').write_text(json.dumps(status,indent=1)+'\n');print(d,Counter(status.values()))
if __name__=='__main__':test(int(sys.argv[1]),int(sys.argv[2]))
