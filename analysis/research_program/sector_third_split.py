"""Split each remaining four-root class at longitudinal distance three."""
import hashlib,json,shutil,subprocess,sys
from pathlib import Path
from . import four_root_sector as joint
from .sector_perimeter_split import rotated_units,continuation,verify,n,coverage

dest=Path('target/sector_third');digest='ef70e47f0be33f4edaaa1b31adebd841f9c2ca8462c25b451c2a06d667354f2e'
def orbit(c):
    return {tuple(sorted(rotated_units(c,g))) for g in range(8)}
def cases():
    parents=joint.cases()
    for m in (7,11):del parents[f'011101010101_{m}']
    members={};cs={}
    for name,p in parents.items():
        w=name[:12]
        for m in range(16):
            c=p+continuation(w,m,3)
            assert len(set(map(abs,c)))==20
            O=orbit(c);k=min(O)
            if k not in members:members[k]=O;cs[f'{name}_{m}']=c
    physical={c for O in members.values() for c in O}
    assert sum(map(len,members.values()))==len(physical)==144*16
    print('20 parent orbits; 320 representative/mask pairs;',len(physical),'physical assignments;',len(cs),'D4 classes',flush=True)
    return cs

def search(cs,limit,dest=dest):
    from pysat.solvers import Solver
    out=dest/'search.json'
    res=json.loads(out.read_text()) if '--resume' in sys.argv else {}
    with joint.src.open('rb') as inp,Solver(name='cadical195') as s:
        assert inp.readline().split()==[b'p',b'cnf',b'2532880',b'17482076']
        for l in inp:s.add_clause(list(map(int,l.split()[:-1])))
        for k,c in cs.items():
            if res.get(k) in ('UNSAT','SAT'):continue
            s.conf_budget(limit);v=s.solve_limited(assumptions=c)
            res[k]={False:'UNSAT',True:'SAT',None:'UNKNOWN'}[v]
            if v:
                x=set(s.get_model());rows=[''.join('#' if 1+i*n+j in x else '.' for j in range(n)) for i in range(n)]
                score=verify(rows);assert score[0]==score[-1]==4078
                (dest/(k+'.forest')).write_text('\n'.join(rows)+'\n');print('verified',score,flush=True)
            print(k,res[k],flush=True);out.write_text(json.dumps(res,indent=2))

def prove(cs,keys,seconds,dest=dest):
    assert keys and len(keys)==len(set(keys)) and set(keys)<=cs.keys()
    tag=dest/('proof_'+str(len(keys)));fn=tag.with_suffix('.cnf');pr=tag.with_suffix('.drat')
    with joint.src.open('rb') as inp,fn.open('wb') as out:
        _,_,nv,nc=inp.readline().split();nv=int(nv)
        ids=list(range(nv+1,nv+1+len(keys)));extra=[ids]+[[-i,x] for i,k in zip(ids,keys) for x in cs[k]]
        out.write(f'p cnf {ids[-1]} {int(nc)+len(extra)}\n'.encode());shutil.copyfileobj(inp,out)
        for c in extra:out.write((' '.join(map(str,c))+' 0\n').encode())
    r=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(fn),str(pr)],capture_output=True)
    assert r.returncode==20,r.stdout[-200:]
    r=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True)
    assert r.returncode==0 and b's VERIFIED' in r.stdout
    tag.with_suffix('.check').write_bytes(r.stdout)
    tag.with_suffix('.json').write_text(json.dumps(keys))
    print('s VERIFIED:',len(keys),'D4 classes;',sum(len(orbit(cs[k])) for k in keys),'physical assignments',flush=True)

def certified(cs):
    neg=[]
    for k in cs:
        w,b,m=k.split('_');b,m=int(b),int(m)
        if w.startswith('0111'):
            live=m.bit_count()>=3 or (w=='011101010101' and m==3)
        elif b!=15:live=m in (b,15)
        else:live=m.bit_count()>=2
        if not live:neg.append(k)
    assert len(neg)==211
    return neg
if __name__=='__main__':
    dest.mkdir(exist_ok=True);coverage();cs=cases()
    with joint.src.open('rb') as s:assert hashlib.file_digest(s,'sha256').hexdigest()==digest
    if sys.argv[1]=='search':search(cs,int(sys.argv[2]))
    elif sys.argv[1]=='prove':
        res=json.loads((dest/'search.json').read_text());assert set(res)==set(cs)
        prove(cs,[k for k,v in res.items() if v=='UNSAT'],int(sys.argv[2]))
    elif sys.argv[1]=='certified':
        prove(cs,certified(cs),int(sys.argv[2]))
        prove(cs,['011101010101_15_3'],int(sys.argv[2]))
