"""Exhaustive sixth-site refinement of the side-109 fifth-site survivors."""
import sys,json,hashlib
from pathlib import Path
import shutil,subprocess
from . import sector_fifth_split as fifth, sector_third_split as sat
from .sector_perimeter_split import continuation,coverage

dest=Path('target/sector_sixth')
def cases():
    old=fifth.cases();dead=set().union(*fifth.certificates(old))
    parents={k:p for k,p in old.items() if k not in dead}
    assert len(parents)==111
    seen=set();covered=set();cs={}
    for k,p in parents.items():
        for m in range(16):
            c=p+continuation(k[:12],m,6)
            assert len(set(map(abs,c)))==32
            orb=sat.orbit(c);key=min(orb)
            if key in seen:continue
            assert covered.isdisjoint(orb)
            seen.add(key);covered.update(orb);cs[f'{k}_{m}']=c
    assert len(covered)==848*16
    print('sixth sites: 111 parents, 1776 representative/mask pairs,',
          len(cs),'orbits covering',len(covered),'physical assignments',flush=True)
    return cs

def grouped_proof(cs,keys,path,seconds):
    """Expose common units before search, instead of hiding them behind selectors."""
    common=set.intersection(*(set(cs[k]) for k in keys))
    with sat.joint.src.open('rb') as inp,path.with_suffix('.cnf').open('wb') as out:
        _,_,nv,nc=inp.readline().split();nv=int(nv)
        ids=list(range(nv+1,nv+1+len(keys)))
        extra=[[x] for x in sorted(common)]+[ids]+[[-i,x] for i,k in zip(ids,keys) for x in cs[k] if x not in common]
        # Precisely the union of the requested cubes after projecting selectors.
        for k in cs:
            c=set(cs[k])
            if common<=c:
                assert any(set(cs[q])-common<=c for q in keys)==(k in keys)
        out.write(f'p cnf {ids[-1]} {int(nc)+len(extra)}\n'.encode());shutil.copyfileobj(inp,out)
        for c in extra:out.write((' '.join(map(str,c))+' 0\n').encode())
    cnf=str(path.with_suffix('.cnf'));pr=str(path.with_suffix('.drat'))
    r=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),cnf,pr],capture_output=True)
    if r.returncode==0:return False
    assert r.returncode==20
    r=subprocess.run(['target/drat-trim/drat-trim',cnf,pr],capture_output=True)
    assert r.returncode==0 and b's VERIFIED' in r.stdout
    path.with_suffix('.check').write_bytes(r.stdout)
    path.with_suffix('.json').write_text(json.dumps(keys))
    print(path.name,'s VERIFIED',len(keys),'orbits',flush=True)
    return True

def batches(cs,seconds):
    r=json.loads((dest/'search.json').read_text())
    first=set(json.loads((dest/'proof_1474.json').read_text()))
    assert b's VERIFIED' in (dest/'proof_1474.check').read_bytes()
    rem=[k for k in cs if r[k]=='UNSAT' and k not in first]
    for group in sorted({k[:12] for k in rem}):
        keys=[k for k in rem if k.startswith(group)]
        name=dest/('batch_'+group)
        if not grouped_proof(cs,keys,name,seconds):
            for k in keys:assert grouped_proof(cs,[k],dest/('case_'+k),seconds)

manifest=Path(__file__).with_name('sector_sixth_proofs.json')
def archive(cs):
    groups={};dead=set()
    for ch in sorted(dest.glob('*.check')):
        keys=json.loads(ch.with_suffix('.json').read_text());assert b's VERIFIED' in ch.read_bytes()
        assert len(set(keys))==len(keys) and dead.isdisjoint(keys);dead.update(keys)
        with ch.with_suffix('.cnf').open('rb') as f:h=hashlib.file_digest(f,'sha256').hexdigest()
        mask={}
        for k in keys:
            assert k in cs
            p,m=k.rsplit('_',1);mask[p]=mask.get(p,0)|(1<<int(m))
        groups[ch.stem]=[h,mask]
    assert len(dead)==1511
    manifest.write_text(json.dumps(groups,indent=1)+'\n')

def certified(cs,seconds,recheck):
    groups=json.loads(manifest.read_text());dead=set()
    for tag,(h,mask) in groups.items():
        keys=[k for k in cs if mask.get(k.rsplit('_',1)[0],0)&(1<<int(k.rsplit('_',1)[1]))]
        assert len(keys)==sum(v.bit_count() for v in mask.values()) and dead.isdisjoint(keys);dead.update(keys)
        path=dest/tag
        if recheck:
            if tag=='proof_1474':sat.prove(cs,keys,seconds,dest)
            else:assert grouped_proof(cs,keys,path,seconds)
        with path.with_suffix('.cnf').open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==h
        assert keys==json.loads(path.with_suffix('.json').read_text()) and b's VERIFIED' in path.with_suffix('.check').read_bytes()
    live=set(cs)-dead
    print('certificates',len(groups),'excluded orbits',len(dead),'remaining',len(live),
          'remaining physical',sum(len(sat.orbit(cs[k])) for k in live),flush=True)

if __name__=='__main__':
    dest.mkdir(exist_ok=True);coverage();cs=cases()
    with sat.joint.src.open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==sat.digest
    if sys.argv[1]=='search':sat.search(cs,int(sys.argv[2]),dest)
    elif sys.argv[1]=='prove':
        r=json.loads((dest/'search.json').read_text());assert set(r)==set(cs)
        sat.prove(cs,[k for k in cs if r[k]=='UNSAT'],int(sys.argv[2]),dest)
    elif sys.argv[1]=='batches':batches(cs,int(sys.argv[2]))
    elif sys.argv[1]=='archive':archive(cs)
    elif sys.argv[1] in ('certified','audit'):certified(cs,int(sys.argv[2]) if len(sys.argv)>2 else 5400,sys.argv[1]=='certified')
