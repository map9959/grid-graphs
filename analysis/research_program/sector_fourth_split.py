"""Fourth-site refinement of precisely the 83 still-live third-site orbits."""
import sys,json,hashlib
from pathlib import Path
from . import sector_third_split as prev
from .sector_perimeter_split import continuation,coverage

dest=Path('target/sector_fourth')
def cases():
    old=prev.cases()
    dead=set(prev.certified(old))|{'011101010101_15_3'}
    parents={k:c for k,c in old.items() if k not in dead};assert len(parents)==83
    seen=set();res={};all_assign=set()
    for name,p in parents.items():
        for m in range(16):
            c=p+continuation(name[:12],m,4)
            assert len(set(map(abs,c)))==24
            orb=prev.orbit(c);key=min(orb)
            if key in seen:continue
            assert all_assign.isdisjoint(orb)
            seen.add(key);all_assign.update(orb);res[f'{name}_{m}']=c
    assert len(all_assign)==624*16
    print('fourth sites: 83 parents, 1328 representative/mask pairs,',
          len(res),'orbits covering',len(all_assign),'physical assignments',flush=True)
    return res

def proof_groups(cs):
    # One all-ones fourth mask per parent. Exceptions retained by the
    # first combined proof are recorded as parent -> other masks.
    exceptions={
        '011101010101_15_7':[7], '011101010101_15_11':[11],
        '011101100101_15_7':[13],
        '111101010101_7_7':[7], '111101010101_15_7':[7], '111101010101_15_15':[7],
        '111101010110_7_7':[7], '111101010110_11_11':[11],
        '111101010110_13_13':[13], '111101010110_14_14':[14],
        '111101010110_15_7':[7], '111101010110_15_11':[11],
        '111101010110_15_13':[13], '111101010110_15_14':[14],
        '111101010110_15_15':[7,11,13,14], '111101011010_7_7':[7],
        '111101011010_11_11':[11], '111101011010_15_7':[7],
        '111101011010_15_11':[11], '111101100110_7_7':[7], '111101100110_15_7':[7],
    }
    first=[];second=[]
    for k in cs:
        parent,t=k.rsplit('_',1)
        if t=='15':continue
        if int(t) not in exceptions.get(parent,[]):first.append(k)
        elif k.startswith('0111'):second.append(k)
    assert (len(first),len(second))==(1160,3)
    return first,second

if __name__=='__main__':
    dest.mkdir(exist_ok=True);coverage();cs=cases()
    with prev.joint.src.open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==prev.digest
    if sys.argv[1]=='search':prev.search(cs,int(sys.argv[2]),dest)
    elif sys.argv[1]=='prove':
        result=json.loads((dest/'search.json').read_text());assert set(result)==set(cs)
        prev.prove(cs,[k for k in cs if result[k]=='UNSAT'],int(sys.argv[2]),dest)
    elif sys.argv[1]=='certified':
        for keys in proof_groups(cs):prev.prove(cs,keys,int(sys.argv[2]),dest)
