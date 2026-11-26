"""Certify subdisjunctions of the shared full-board port/site formula."""
from pathlib import Path
from hashlib import file_digest
import gzip,json,shutil,subprocess,sys

def make(a,b,lo,hi,fn,local=0):
    base=Path('target/southwest_ports_5_191_102_160'+('_SWlocal' if local else '')+'.cnf')
    assert 102<=a<=b<=160 and lo in range(5,192,6) and hi in range(lo,192,6)
    meta=json.loads(gzip.decompress(base.with_suffix('.ids.gz').read_bytes()))
    with base.open('rb') as src,fn.open('wb') as dst:
        _,_,nv,nc=src.readline().split();nv=int(nv)
        dst.write(f'p cnf {nv} {int(nc)+2}\n'.encode())
        assert [nv-58+s-102 for s in range(102,161)]==[meta['ports'][str(s)] for s in range(102,161)]
        dst.write((' '.join(str(meta['ports'][str(s)]) for s in range(a,b+1))+' 0\n').encode())
        shutil.copyfileobj(src,dst)
        dst.write((' '.join(str(meta['flags'][str(d)]) for d in range(lo,hi+1,6))+' 0\n').encode())

def batch(a,b,lo,hi,seconds,local=0):
    stem=Path(f'target/sw_port_batch_{a}_{b}_{lo}_{hi}'+('_local' if local else ''))
    fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
    make(a,b,lo,hi,fn,local)
    with fn.open('rb') as src:print('starts',a,b,'distances',lo,hi,'sha256',file_digest(src,'sha256').hexdigest(),flush=True)
    with stem.with_suffix('.log').open('w') as out:st=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(fn),str(pr)],stdout=out).returncode
    if st==20:
        with stem.with_suffix('.check').open('wb') as out:subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],stdout=out,check=True)
        assert b's VERIFIED' in stem.with_suffix('.check').read_bytes()
        print('s VERIFIED',a,b,lo,hi,flush=True)
    elif st==10 and not local:
        from .extend_forest_28 import verify
        model={int(z) for l in stem.with_suffix('.log').read_text().splitlines() if l.startswith('v ') for z in l[2:].split()}
        meta=json.loads(gzip.decompress(Path('target/southwest_ports_5_191_102_160.ids.gz').read_bytes()))
        rows=[''.join('#' if z in model else '.' for z in meta['marks'][i*245:(i+1)*245]) for i in range(245)]
        score=verify(rows);assert score[0]==score[-1]==20240;print('TREE',score)
        stem.with_suffix('.tree').write_text('\n'.join(rows)+'\n')
    else:print('local SAT; physical replay required' if st==10 else 'UNKNOWN')
if __name__=='__main__':batch(*map(int,sys.argv[1:]))
