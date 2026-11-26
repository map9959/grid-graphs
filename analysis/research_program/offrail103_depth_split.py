"""Disjoint first-empty-depth split of the uncapped >=7-deletion model."""
import hashlib,json,shutil,subprocess,sys
from pathlib import Path
from .extend_forest_28 import verify

ROOT=Path('target')
BASE=ROOT/'sector103_3647_deep_matching_component_offrail9_bins24_mincollar7_depth10_count.cnf'
N=103
def band(g,d):
    def site(i,j):
        if g%2:i,j=j,i
        if g==2:i=N-1-i
        if g==3:j=N-1-j
        return 1+i*N+j
    return [site(i,j) for i in range(max(0,d-1),d+2) for j in range(N) if j%3]

def clauses(depth,nv):
    # depth 11 is the no-empty-neighborhood case.
    assert 0<=depth<=11
    a=[band(g,d) for d in range(depth) for g in range(4)]
    if depth<11:
        flags=list(range(nv+1,nv+5));a.append(flags)
        for g,v in enumerate(flags):
            a.extend([[-v,-m] for m in band(g,depth)])
    return a

def solve(depth,sec):
    dest=ROOT/'offrail103_depth_split';dest.mkdir(exist_ok=True)
    stem=dest/f'd{depth}';cnf=stem.with_suffix('.cnf');drat=stem.with_suffix('.drat')
    with BASE.open('rb') as inp,cnf.open('wb') as out:
        _,_,nv,nc=inp.readline().split();nv,nc=int(nv),int(nc)
        a=clauses(depth,nv)
        out.write(f'p cnf {nv+4*(depth<11)} {nc+len(a)}\n'.encode())
        shutil.copyfileobj(inp,out)
        for c in a:out.write((' '.join(map(str,c))+' 0\n').encode())
    with cnf.open('rb') as f:digest=hashlib.file_digest(f,'sha256').hexdigest()
    with stem.with_suffix('.log').open('wb') as fd:
        rc=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(cnf),str(drat)],stdout=fd).returncode
    if rc==20:
        out=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(drat)],check=True,capture_output=True).stdout
        assert b's VERIFIED' in out;stem.with_suffix('.check').write_bytes(out)
        verdict='VERIFIED UNSAT'
    elif rc==10:
        model={int(v) for line in stem.with_suffix('.log').read_text().splitlines() if line.startswith('v ') for v in line[2:].split()}
        rows=[''.join('#' if i*N+j+1 in model else '.' for j in range(N)) for i in range(N)]
        result=verify(rows);assert result[-1]>=3647
        stem.with_suffix('.txt').write_text('\n'.join(rows)+'\n');verdict=str(result)
    else:
        assert rc==0 and 'UNKNOWN' in stem.with_suffix('.log').read_text()
        drat.unlink(missing_ok=True);verdict='UNKNOWN'
    stem.with_suffix('.json').write_text(json.dumps(dict(depth=depth,seconds=sec,sha256=digest,result=verdict))+'\n')
    cnf.unlink();print(depth,verdict,digest,flush=True)
if __name__=='__main__':
    for d in map(int,sys.argv[2:]):solve(d,int(sys.argv[1]))
