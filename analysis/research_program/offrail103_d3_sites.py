"""Exact depth-three east site split, sharing proofs across the parent signatures."""
from collections import Counter
from pathlib import Path
import hashlib,json,sys,subprocess
from pysat.solvers import Solver
from .offrail103_one_depth import BASE,HASH,N,group_cut,suffix,verify
from .offrail103_joint_summary import report

OUT=Path('target/offrail103_d3_sites')
SOUTH=Path('target/offrail103_joint_south')
SITES=[1+i*N+j for i in (7,8) for j in (96,95,94)]

def build(mode):
    north=mode=='north'
    source=Path('target/offrail103_joint35/crop_union.cnf') if north else SOUTH/'d3_uniona.cnf' if mode!='board' else BASE
    with source.open('rb') as fd:
        h=hashlib.file_digest(fd,'sha256').hexdigest()
    south=mode not in ('board','north')
    assert h==('e415c70e69ae07e741ec5911a6095034f9b8c0f40ce0cb5dd6c367a8d0c28859' if north else '2595d7ad7a9167df323f2013f09b70618491183823ee30a7407c20df822849b5' if south else HASH)
    with source.open('rb') as fd:_,_,top,nc=fd.readline().split();top=int(top);nc=int(nc)-int(south or north)
    pairs=['-'.join(p) for p in report()[3]]
    prior=json.loads((SOUTH/'d3.json').read_text())
    live=[k for k in pairs if not prior[k].startswith('VERIFIED') and all('2' in m for m in k.split('-'))]
    assert len(live)==73
    rows=[]
    if south:
        parent={k:top-len(pairs)+t+1 for t,k in enumerate(pairs) if k in live}
        sites=[1+(N-1-(x-1)//N)*N+(x-1)%N for x in SITES]
    else:
        if north:
            from .offrail103_one_depth import band
            rows=[[-v] for v in band(0,3) if min((v-1)%N,N-1-(v-1)%N)<30]
        else:top,rows=suffix(3,top)
        first=top+1;top,g=group_cut(top,'west');rows.extend(g)
        sites=SITES;parent={}
        for k in live:
            top+=1;parent[k]=top
            for i in range(12):
                x=first+i;rows.append([-top,x if str(i%6) in k.split('-')[i//6] else -x])
    rows.append(list(parent.values()));mask={}
    for m in range(1,64):
        top+=1;mask[m]=top
        rows.extend([[-top,x if m>>i&1 else -x] for i,x in enumerate(sites)])
    if mode=='mask':cases={f'{m:02x}':z for m,z in mask.items()}
    else:
        prev=json.loads((OUT/'mask.json').read_text())
        tables=[json.loads((OUT/f'{s}.json').read_text()) for s in ('local','local_remote')] if north else []
        cases={}
        for k,z in parent.items():
            for m,y in mask.items():
                if prev[f'{m:02x}'].startswith('VERIFIED'):continue
                if north and ('125' in k.split('-') or any(t[f"{k.split('-')[1]}@{m:02x}"]=='VERIFIED' for t in tables)):continue
                top+=1;cases[f'{k}@{m:02x}']=top;rows.extend([[-top,z],[-top,y]])
    return source,nc,rows,top,cases

def run(mode,budget):
    OUT.mkdir(exist_ok=True)
    src,nc,rows,top,cases=build(mode)
    status={}
    with Solver(name='cadical195') as solver:
        with src.open('rb') as fd:
            fd.readline()
            for _ in range(nc):solver.add_clause(list(map(int,fd.readline().split()[:-1])))
        solver.append_formula(rows)
        for k,v in cases.items():
            solver.conf_budget(budget);res=solver.solve_limited(assumptions=[v])
            if res is False:status[k]='pending'
            elif res is None:status[k]='UNKNOWN'
            elif mode!='board':status[k]='crop SAT'
            else:
                pos=set(solver.get_model());board=[''.join('#' if 1+i*N+j in pos else '.' for j in range(N)) for i in range(N)]
                score=verify(board);assert score[-1]>=3647
                (OUT/f'tree_{k}.txt').write_text('\n'.join(board)+'\n');status[k]=str(score)
    def certify(keys,tag):
        if not keys:return
        p=OUT/f'{mode}_{tag}.cnf';pr=p.with_suffix('.drat')
        with src.open('rb') as fd,p.open('wb') as dst:
            fd.readline();dst.write(f'p cnf {top} {nc+len(rows)+1}\n'.encode())
            for _ in range(nc):dst.write(fd.readline())
            for ls in rows+[[cases[k] for k in keys]]:dst.write((' '.join(map(str,ls))+' 0\n').encode())
        with p.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t','120',str(p),str(pr)],stdout=fd).returncode
        if rc==20:
            data=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],check=True,capture_output=True).stdout
            assert b's VERIFIED' in data;p.with_suffix('.check').write_bytes(data)
            for k in keys:status[k]='VERIFIED '+tag
        elif rc==0 and len(keys)>15:
            p.unlink();pr.unlink(missing_ok=True);i=len(keys)//2;certify(keys[:i],tag+'a');certify(keys[i:],tag+'b')
        else:assert rc==0
    certify([k for k,v in status.items() if v=='pending'],'union')
    (OUT/f'{mode}.json').write_text(json.dumps(status,indent=1)+'\n')
    print(mode,len(cases),Counter(status.values()))
if __name__=='__main__':run(sys.argv[1],int(sys.argv[2]))
