"""Eighth-site refinement of every surviving side-109 perimeter signature."""
import hashlib,json
from pathlib import Path
from . import sector_seventh_split as prev
from .sector_perimeter_split import continuation
from .sector_third_split import orbit

dest=Path('target/sector_eighth')
manifest=Path(__file__).with_name('sector_eighth_proofs.json')

def cases():
    old=prev.cases()
    assert hashlib.sha256(prev.manifest.read_bytes()).hexdigest()=='35bf908bc04f60ec61bf3b144b69a0cf8df24b02e78b8f05cdb34784dd8911a1'
    dead=set()
    for _,mask in json.loads(prev.manifest.read_text()).values():
        keys={k for k in old if mask.get(k.rsplit('_',1)[0],0)&(1<<int(k.rsplit('_',1)[1]))}
        assert len(keys)==sum(v.bit_count() for v in mask.values()) and dead.isdisjoint(keys)
        dead.update(keys)
    parents={k:p for k,p in old.items() if k not in dead}
    assert len(parents)==228
    seen=set();physical=set();cs={}
    for k,p in parents.items():
        for m in range(16):
            c=p+continuation(k[:12],m,8)
            assert len(set(map(abs,c)))==40
            O=orbit(c);key=min(O)
            if key in seen:continue
            assert physical.isdisjoint(O)
            seen.add(key);physical.update(O);cs[f'{k}_{m}']=c
    assert len(physical)==1760*16
    print('eighth sites: 228 parents, 3648 representative/mask pairs,',len(cs),
          'orbits covering',len(physical),'physical assignments',flush=True)
    return cs

if __name__=='__main__':prev.main(cases(),dest,manifest)
