"""Weaken certified end masks to the actual port clauses needed by their proofs."""
from hashlib import file_digest
from pathlib import Path
import gzip,json,sys,subprocess
from .southwest_ports import patterns

base=Path('target/southwest_ports_5_191_102_160.cnf')
def hashfile(p):
    with p.open('rb') as f:return file_digest(f,'sha256').hexdigest()

def guards(a,b):
    meta=json.loads(gzip.decompress(base.with_suffix('.ids.gz').read_bytes()));masks=patterns()
    return {(-meta['ports'][str(s)],meta['marks'][i*245+j]*(1 if val else -1)):(s,i,j,val)
            for s in range(a,b+1) for (i,j),val in masks[s].items()}

def checked(cmd,log):
    with log.open('wb') as out:subprocess.run(cmd,stdout=out,check=True)
    assert b's VERIFIED' in log.read_bytes()

def trim(a,b):
    stem=Path(f'target/sw_port_batch_{a}_{b}_5_191')
    fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
    small=stem.with_suffix('.small');core=stem.with_suffix('.core');checker='target/drat-trim/drat-trim'
    checked([checker,str(fn),str(pr),'-C','-l',str(small),'-c',str(core)],stem.with_suffix('.trimlog'))
    lits=guards(a,b);keep=set()
    with core.open() as f:
        for line in f:
            if line.startswith('p'):continue
            vs=line.split()
            if len(vs)==3:
                x,y=map(int,vs[:2])
                if (x,y) in lits:keep.add((x,y))
                if (y,x) in lits:keep.add((y,x))
    drop=set(lits)-keep;weak=stem.with_suffix('.weak.cnf');skip={f'{x} {y} 0\n'.encode() for x,y in drop}
    count=0
    with fn.open('rb') as src,weak.open('wb') as dst:
        _,_,nv,nc=src.readline().split()
        dst.write(b'p cnf '+nv+b' '+str(int(nc)-len(skip)).encode()+b'\n')
        for line in src:
            if line in skip:count+=1
            else:dst.write(line)
    assert count==len(skip)
    checked([checker,str(weak),str(small)],stem.with_suffix('.weakcheck'))
    bits={s:sorted((i,j,v) for g in keep for k,i,j,v in (lits[g],) if k==s) for s in range(a,b+1)}
    record={'base':hashfile(base),'batch':hashfile(fn),'weakened':hashfile(weak),'proof':hashfile(small),'bits':bits}
    stem.with_suffix('.json').write_text(json.dumps(record,separators=(',',':'))+'\n')
    print('checked weakened end masks',a,b,'bits retained per pair',[len(bits[s]) for s in bits],
          'weak hash',record['weakened'],flush=True)
    core.unlink();weak.unlink()
if __name__=='__main__':trim(*map(int,sys.argv[1:]))
