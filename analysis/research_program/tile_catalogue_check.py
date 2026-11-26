"""Independent DRAT coverage of each physical 6x6 mask projection."""
import gzip,json,subprocess,sys
from pathlib import Path
from hashlib import sha256
from itertools import product
from .tile_family_lp import typ,L
from .defect_window import table,window,DIR
from .slit_star_transfer import frame_path

def verify(lo,hi):
    n=119;k=39;K=38;w=3;d=5;folder=Path('target/tile_catalogue_proofs');folder.mkdir(exist_ok=True)
    raw=Path('target/tile_family_3_5_h6.json.gz').read_bytes();B={tuple(r[:2]):r[2] for r in json.loads(gzip.decompress(raw))}
    T=table(n);marks,path=frame_path(n,w)
    reps={tuple(typ(i,K) for i in p):p for p in product(range(K),repeat=2)};summary=[]
    for key,(i,j) in sorted(reps.items()):
        if not lo<=key[0]<=hi:continue
        x,y=1+3*i,1+3*j;dom=set(product(range(max(0,x-6),min(n,x+12)),range(max(0,y-6),min(n,y+12))))
        flag=all((2+a,d+b) in dom for a,b in ((0,0),*DIR))
        def emit(f,bit,flags):
            for p in sorted(dom & marks.keys()):f.append([bit(*p)*(1 if marks[p] else -1)])
            for block in B[key]:
                f.append([bit(x+3*h+a,y+3*l+b)*(-1 if m>>(3*a+b)&1 else 1)
                          for (h,l),m in zip(product(range(2),repeat=2),block) for a,b in product(range(3),repeat=2)])
            stem=folder/f'word_{key[0]}_{key[1]}';fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
            f.to_file(str(fn))
            with stem.with_suffix('.log').open('wb') as o:assert subprocess.run(['target/cadical/build/cadical',str(fn),str(pr)],stdout=o).returncode==20
            out=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True,check=True).stdout
            assert b's VERIFIED' in out
            summary.append((key,len(B[key]),sha256(fn.read_bytes()).hexdigest(),sha256(pr.read_bytes()).hexdigest()))
            fn.unlink();stem.with_suffix('.log').unlink()
        window(n,'rim',1,T,want=flag,defects={('s',2,d)},root_site=(118,118),orient=path,domain=dom,emit=emit)
    (folder/f'manifest_{lo}_{hi}.json').write_text(json.dumps({'catalogue':sha256(raw).hexdigest(),'proofs':summary},separators=(',',':')))
    print('s VERIFIED',len(summary),'complete physical catalogues, type rows',lo,hi,flush=True)
if __name__=='__main__':verify(*map(int,sys.argv[1:]))
