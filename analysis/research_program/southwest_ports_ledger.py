"""Verify the southwest completion case cover. Regenerate sub-CNFs from one base."""
from hashlib import file_digest
from pathlib import Path
from tempfile import TemporaryDirectory
from itertools import product
import gzip,json,re,subprocess,sys
from .sw_port_batch import make
from .southwest_ports import patterns
from .depth_two_203_ledger import checked
from .shortening_ledger import SWEEP
from .zipper_rails import build,verify

BASE='cd5366fad219c70f73f7d2baf43a2d6c6fc8c2eb551f47ee1a1cb6bc623215e4'
LOCAL_BASE='c0ea2ed713e5753dce2028cc3552efc9c186a6fc36794acfe0d1e68528b95b7c'
LOCAL=[
    (102,121,'cda466f260f81845b155d0f91c783861076b90256f6612a9fd1f29986cce069a'),
    (122,141,'2ba558ca0e3ae4b9d3e930a4920bb4504c6722aa60fdebc6203080bdb2597ad6'),
    (142,160,'f0a32b49b7c065ddc49d6fbb7817d9dda1197fc80607ba5d0028d424d83201b8')]
GROUPS=[
    (102,111,'2ebba91d002241aa6bf6e0a836f91d917ef9e9c689509846aa074bfb5d6be223'),
    (112,121,'593f62f402ca3e4f2962cd54dc1620335df5c743ba9f9ae3d3fec27273d5d475'),
    (122,131,'f64b1cd55a7e823062a33df36a6f8c8731b99d5be45a2ed46e23882568684bfa'),
    (132,141,'5bac37655bf12e47f48f7c4232dd1eb472e9208a60664e0617c609c16682bb0b'),
    (142,149,'7eabeb02c66f89dcedf488fdd50820bad2bd7f7854a02a27914dfc5eb227ad25'),
    (150,150,'bae092a31ed83a1256b6337a25a0783810ab35677d4c1eef14b1917e1f83103e'),
    (151,160,'23aee554e826e977901f124ebb9286e767fbc2e28fe14b7aecd84385ef7d489c')]

def digest(path):
    with path.open('rb') as f:return file_digest(f,'sha256').hexdigest()

def verify_groups(groups,basehash,local=0):
    src=Path('target/southwest_ports_5_191_102_160'+('_SWlocal' if local else '')+'.cnf')
    assert digest(src)==basehash
    ids=json.loads(gzip.decompress(src.with_suffix('.ids.gz').read_bytes()))
    ends=patterns();assert set(ends)==set(range(102,161)) and all(len(m)==204 for m in ends.values())
    ds=range(5,192,6);assert set(map(int,ids['flags']))==set(ds) and len(set(ids['marks']))==245**2
    # Check the actual 59-by-204 guarded bit constraints, not just cardinalities.
    guards={f"{-ids['ports'][str(s)]} {ids['marks'][245*i+j]*(1 if v else -1)} 0\n".encode()
            for s,marks in ends.items() for (i,j),v in marks.items()}
    def clause(vs):return (' '.join(map(str,vs))+' 0\n').encode()
    guards.add(clause(ids['flags'][str(d)] for d in ds))
    guards.add(clause(ids['ports'][str(s)] for s in range(102,161)))
    for i,j in product(range(102,237),range(8,143)):
        guards.add(clause(ids['marks'][245*x+y] for x,y in ((i,j),(i+1,j),(i-1,j),(i,j+1),(i,j-1))))
    with src.open('rb') as f:
        for l in f:guards.discard(l)
    assert not guards
    seen=set()
    with TemporaryDirectory(dir='target') as tmp:
        for a,b,h in groups:
            stem=Path(f'target/sw_port_batch_{a}_{b}_5_191'+('_local' if local else ''))
            fn=Path(tmp)/'replay.cnf';make(a,b,5,191,fn,local)
            assert digest(fn)==h
            log=stem.with_suffix('.check')
            if '--drat' in sys.argv:
                recheck=Path(tmp)/'dratcheck'
                with recheck.open('wb') as out:subprocess.run(['target/drat-trim/drat-trim',str(fn),str(stem.with_suffix('.drat'))],stdout=out,check=True)
                assert b's VERIFIED' in recheck.read_bytes()
            text=log.read_text();assert 's VERIFIED' in text
            steps,=re.findall(r'using (\d+) resolution steps',text)
            cells=set(product(range(a,b+1),ds,(0,1),range(8)))
            assert seen.isdisjoint(cells);seen.update(cells)
            print('s VERIFIED starts',a,b,'cases',len(cells),'resolution steps',steps)
    return seen

def run():
    for k,h in enumerate(SWEEP):checked(f'star_strip_5_5_1_0_sw{k}',h)
    seen=verify_groups(GROUPS,BASE)
    assert seen==set(product(range(102,161),range(5,192,6),(0,1),range(8)))
    print('full forest: 59 mask pairs x 64 sites x 8 frames =',len(seen),'excluded')
    assert verify_groups(LOCAL,LOCAL_BASE,1)==seen
    # The weaker input is byte-for-byte a subsequence of the full one
    # after the header. Only the guarded turn sheet equalities are absent.
    prefix='target/southwest_ports_5_191_102_160'
    with open(prefix+'.cnf','rb') as src,open(prefix+'_SWlocal.cnf','rb') as dst:
        src.readline();dst.readline();nextline=dst.readline();dropped=0
        for line in src:
            if line==nextline:nextline=dst.readline();continue
            vs=line.split();assert len(vs)==5 and vs[0].startswith(b'-') and vs[1].startswith(b'-') and vs[-1]==b'0'
            dropped+=1
        assert not nextline and dropped==2*(12*135**2+6*4*135)
    print('verified clause subsequence; omitted',dropped,'turn-sheet clauses')
    print('original regional forest + southwest local constraints ONLY: same',len(seen),'excluded')
    masks=patterns()
    assert len(set().union(*(set(m) for m in masks.values())))==59*204
    print('disjoint end sites:',59*204,'; every upper witness must change at least 59 donor bits there')
    from .southwest_port_core import guards
    record=json.loads((Path(__file__).with_name('one_gap_projection_examples')/'sw150_weak.json').read_text())
    bits={tuple(v) for v in record['bits']['150']}
    port=patterns()[150]
    assert len(bits)==142 and all(port.get((i,j))==v for i,j,v in bits)
    skip={f'{x} {y} 0\n'.encode() for (x,y),(_,i,j,v) in guards(150,150).items() if (i,j,v) not in bits}
    assert len(skip)==62
    with TemporaryDirectory(dir='target') as tmp:
        src=Path(tmp)/'batch.cnf';weak=Path(tmp)/'weak.cnf'
        make(150,150,5,191,src);n=0
        with src.open('rb') as f,weak.open('wb') as out:
            _,_,nv,nc=f.readline().split();out.write(b'p cnf '+nv+b' '+str(int(nc)-62).encode()+b'\n')
            for line in f:
                if line in skip:n+=1
                else:out.write(line)
        assert n==62 and digest(weak)==record['weakened']
        stem=Path('target/sw_port_batch_150_150_5_191')
        assert 's VERIFIED' in stem.with_suffix('.weakcheck').read_text()
        if '--drat' in sys.argv:
            proof=next(p for p in (stem.with_suffix('.small'),stem.with_suffix('.drat')) if p.exists() and digest(p)==record['proof'])
            with (Path(tmp)/'check').open('wb') as out:subprocess.run(['target/drat-trim/drat-trim',str(weak),str(proof)],stdout=out,check=True)
            assert b's VERIFIED' in (Path(tmp)/'check').read_bytes()
    print('start 150: weakened CNF checked with 71+71 retained bits')
    print('unconditional star sites eliminated by these batches: 0; physical rail',verify(build(245)))
if __name__=='__main__':run()
