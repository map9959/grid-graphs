"""All seventh-site refinements of certified-live sixth-site side-109 classes."""
from pathlib import Path
import hashlib,json,sys
from . import sector_sixth_split as sixth, sector_third_split as sat
from .sector_perimeter_split import continuation,coverage

dest=Path('target/sector_seventh')
manifest=Path(__file__).with_name('sector_seventh_proofs.json')

def cases():
    old=sixth.cases();dead=set()
    assert hashlib.sha256(sixth.manifest.read_bytes()).hexdigest()=='f3af63351d9c2ebe01a71a6bb8fe4d145225d00162e840af61e293db69577028'
    for _,mask in json.loads(sixth.manifest.read_text()).values():
        keys={k for k in old if mask.get(k.rsplit('_',1)[0],0)&(1<<int(k.rsplit('_',1)[1]))}
        assert len(keys)==sum(v.bit_count() for v in mask.values()) and dead.isdisjoint(keys)
        dead.update(keys)
    parents={k:p for k,p in old.items() if k not in dead}
    assert len(parents)==204
    physical=set();seen=set();cs={}
    for k,p in parents.items():
        for m in range(16):
            c=p+continuation(k[:12],m,7)
            assert len(set(map(abs,c)))==36
            orb=sat.orbit(c);key=min(orb)
            if key in seen:continue
            assert physical.isdisjoint(orb)
            physical.update(orb);seen.add(key);cs[f'{k}_{m}']=c
    assert len(physical)==1568*16
    print('seventh sites: 204 parents, 3264 representative/mask pairs,',len(cs),
          'orbits covering',len(physical),'physical assignments',flush=True)
    return cs

def masks(keys):
    ans={}
    for k in keys:
        p,m=k.rsplit('_',1);ans[p]=ans.get(p,0)|(1<<int(m))
    return ans

def main(cs,dest,manifest):
    dest.mkdir(exist_ok=True);coverage()
    with sat.joint.src.open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==sat.digest
    cmd=sys.argv[1]
    if cmd=='search':sat.search(cs,int(sys.argv[2]),dest)
    elif cmd=='prove':
        r=json.loads((dest/'search.json').read_text());assert set(r)==set(cs)
        sat.prove(cs,[k for k in cs if r[k]=='UNSAT'],int(sys.argv[2]),dest)
    elif cmd=='archive':
        groups={};dead=set()
        for ch in sorted(dest.glob('*.check')):
            keys=json.loads(ch.with_suffix('.json').read_text());assert b's VERIFIED' in ch.read_bytes()
            assert len(keys)==len(set(keys)) and dead.isdisjoint(keys) and set(keys)<=cs.keys();dead.update(keys)
            with ch.with_suffix('.cnf').open('rb') as f:h=hashlib.file_digest(f,'sha256').hexdigest()
            groups[ch.stem]=[h,masks(keys)]
        manifest.write_text(json.dumps(groups,indent=1)+'\n')
    elif cmd in ('audit','certified'):
        dead=set()
        for tag,(h,mask) in json.loads(manifest.read_text()).items():
            keys=[k for k in cs if mask.get(k.rsplit('_',1)[0],0)&(1<<int(k.rsplit('_',1)[1]))]
            assert len(keys)==sum(v.bit_count() for v in mask.values()) and dead.isdisjoint(keys);dead.update(keys)
            path=dest/tag
            if cmd=='certified':
                if tag.startswith('proof_'):sat.prove(cs,keys,int(sys.argv[2]),dest)
                else:assert sixth.grouped_proof(cs,keys,path,int(sys.argv[2]))
            with path.with_suffix('.cnf').open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==h
            assert keys==json.loads(path.with_suffix('.json').read_text()) and b's VERIFIED' in path.with_suffix('.check').read_bytes()
        live=cs.keys()-dead
        print('certified exclusions',len(dead),'remaining',len(live),'physical',sum(len(sat.orbit(cs[k])) for k in live),
              'remaining parents',len({k.rsplit('_',1)[0] for k in live}))

if __name__=='__main__':main(cases(),dest,manifest)
