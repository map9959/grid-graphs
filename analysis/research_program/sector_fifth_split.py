"""Distance-five marks on the already chosen side at all four corners."""
from pathlib import Path
import sys,json,hashlib
from . import sector_fourth_split as fourth, sector_third_split as sat
from .sector_perimeter_split import continuation,coverage

dest=Path('target/sector_fifth')
def cases():
    old=fourth.cases()
    excluded=set().union(*fourth.proof_groups(old))
    parents={k:c for k,c in old.items() if k not in excluded}
    assert len(parents)==104
    representatives={};physical=set();seen=set()
    for k,p in parents.items():
        for m in range(16):
            c=p+continuation(k[:12],m,5)
            assert len(set(map(abs,c)))==28
            orb=sat.orbit(c);key=min(orb)
            if key in seen:continue
            assert physical.isdisjoint(orb)
            physical.update(orb);seen.add(key);representatives[f'{k}_{m}']=c
    assert len(physical)==792*16
    print('fifth sites: 104 parents, 1664 representative/mask pairs,',
          len(seen),'orbits covering',len(physical),'physical assignments',flush=True)
    return representatives

def certificates(cs):
    # Compact solver-independent manifests for the two verified disjunctions.
    exceptions={
        '011101010110_15_15_15':[7],
        '111101010101_15_15_15':[7],
        '111101010110_15_15_15':[7,11,13,14],
        '111101011010_15_15_15':[7,11],
        '111101100110_15_15_15':[7],
    }
    first=[]
    for k in cs:
        p,m=k.rsplit('_',1)
        if k=='111101010110_15_15_7_15' or (m!='15' and int(m) not in exceptions.get(p,[])):
            first.append(k)
    second=['011101010110_15_15_15_7']
    assert len(first)==1491 and not set(second)&set(first)
    return first,second

if __name__=='__main__':
    dest.mkdir(exist_ok=True);coverage();cs=cases()
    with sat.joint.src.open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==sat.digest
    if sys.argv[1]=='search':sat.search(cs,int(sys.argv[2]),dest)
    elif sys.argv[1]=='prove':
        result=json.loads((dest/'search.json').read_text());assert set(result)==set(cs)
        sat.prove(cs,[k for k in cs if result[k]=='UNSAT'],int(sys.argv[2]),dest)
    elif sys.argv[1]=='certified':
        for keys in certificates(cs):sat.prove(cs,keys,int(sys.argv[2]),dest)
