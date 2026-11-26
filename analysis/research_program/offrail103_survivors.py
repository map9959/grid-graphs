"""The two surviving physical cases, with a global run/edge count cut."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc
from .offrail103_depth_split import BASE,N,band,verify

def run(case,sec):
    assert case in ('all','one')
    d=Path('target/offrail103_survivors');d.mkdir(exist_ok=True)
    stem=d/case;cnf=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
    with BASE.open('rb') as src,cnf.open('wb') as dest:
        _,_,nv,nc=src.readline().split();nv,nc=int(nv),int(nc)
        pool=IDPool(start_from=nv+1);f=CNF()
        # If there is an exceptional side rotate it north. Every rotation
        # of an actual 3647 board independently meets the >=7 donor theorem.
        for side in range(4):
            for h in range(11):
                if case=='all' or side or h<2:f.append(band(side,h))
        if case=='one':
            flags=[pool.id() for _ in range(9)];f.append(flags)
            for h,z in enumerate(flags,2):
                for u in band(0,h):f.append([-z,-u])
        runs=[];holes=[];isolates=[]
        def mark(i,j):return 1+N*i+j
        for i in range(N):
            for j in range(N):
                x=mark(i,j);v=pool.id();runs.append(v)
                f.append([-x,*([x-N] if i else []),*([x-1] if j else []),v])
                u=pool.id();isolates.append(u)
                f.append([x,*[mark(i+a,j+b) for a,b in ((1,0),(-1,0),(0,1),(0,-1)) if 0<=i+a<N and 0<=j+b<N],u])
                for side in (i in (0,N-1),j in (0,N-1)):
                    if side:
                        w=pool.id();holes.append(w);f.append([x,w])
        f.extend(CardEnc.atmost(holes,43,vpool=pool,encoding=6).clauses)
        from .physical_mark_count import add
        costs=runs+holes+isolates
        add(f,pool,[-v for v in costs],len(costs)-79)
        dest.write(f'p cnf {pool.top} {nc+len(f.clauses)}\n'.encode());shutil.copyfileobj(src,dest)
        for cl in f.clauses:dest.write((' '.join(map(str,cl))+' 0\n').encode())
    with cnf.open('rb') as inp:digest=hashlib.file_digest(inp,'sha256').hexdigest()
    with stem.with_suffix('.log').open('wb') as fd:rc=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(cnf),str(pr)],stdout=fd).returncode
    if rc==20:
        out=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(pr)],check=True,capture_output=True).stdout
        assert b's VERIFIED' in out;stem.with_suffix('.check').write_bytes(out);verdict='VERIFIED UNSAT'
    elif rc==10:
        M={int(v) for l in stem.with_suffix('.log').read_text().splitlines() if l.startswith('v ') for v in l[2:].split()}
        rows=[''.join('#' if mark(i,j) in M else '.' for j in range(N)) for i in range(N)]
        result=verify(rows);assert result[-1]>=3647;verdict=str(result);stem.with_suffix('.txt').write_text('\n'.join(rows)+'\n')
    else:
        assert rc==0 and 'UNKNOWN' in stem.with_suffix('.log').read_text()
        pr.unlink(missing_ok=True);verdict='UNKNOWN'
    stem.with_suffix('.json').write_text(json.dumps(dict(case=case,result=verdict,seconds=sec,sha256=digest))+'\n')
    print(case,verdict,digest,flush=True)
if __name__=='__main__':run(sys.argv[1],int(sys.argv[2]))
