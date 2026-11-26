"""Match labelled site masks to verified union CNFs and deduplicate exclusions."""
from collections import Counter
import hashlib,json,subprocess,sys
from .offrail103_d3_sites import OUT,build,N

def audit(mode):
    src,nc,rows,top,cases=build(mode)
    rec=json.loads((OUT/f'{mode}.json').read_text());assert rec.keys()==cases.keys()
    n=len(cases)
    site_rows=rows[-63*6:] if mode=='mask' else rows[-n*2-63*6:-n*2]
    for i in range(63):
        ls=site_rows[i*6:i*6+6];mask=i+1
        for b,(_,x) in enumerate(ls):
            r,c=divmod(abs(x)-1,N)
            if mode not in ('board','north'):r=N-1-r
            assert (r,c)==(7+b//3,96-b%3) and (x>0)==bool(mask&(1<<b))
    if mode!='mask':
        selected=rows[-n*2:];parents={}
        for i,(key,z) in enumerate(cases.items()):
            a,b=selected[2*i:2*i+2];label,m=key.split('@')
            assert a[0]==b[0]==-z and b[1]==-site_rows[(int(m,16)-1)*6][0]
            assert parents.setdefault(label,a[1])==a[1]
        assert len(set(parents.values()))==len(parents)
        if mode!='north':assert len(parents)==73
        if mode in ('board','north'):
            first=min(rows[-2*n-63*6-1])-12
            pp={v:k.split('-') for k,v in parents.items()}
            got={v:[] for v in pp};defs={}
            for cl in rows:
                if len(cl)==2 and -cl[0] in pp:got[-cl[0]].append(cl[1])
                if first<=-cl[0]<first+12 and len(cl)>2 and all(x>0 for x in cl[1:]):defs[-cl[0]]=cl[1:]
            for v,(west,east) in pp.items():
                assert got[v]==[(first+j)*(1 if str(j%6) in (west,east)[j//6] else -1) for j in range(12)]
            for j in range(12):
                cols=range(6,9) if j<6 else range(94,97)
                assert set(defs[first+j])=={1+N*r+c for r in range(17) if r%3 and r//3==j%6 for c in cols}
    for status in sorted(set(rec.values())):
        if not status.startswith('VERIFIED '):continue
        tag=status.split()[1];p=OUT/f'{mode}_{tag}.cnf';h=hashlib.sha256()
        h.update(f'p cnf {top} {nc+len(rows)+1}\n'.encode())
        with src.open('rb') as fd:
            fd.readline()
            for _ in range(nc):h.update(fd.readline())
        dead=[v for k,v in cases.items() if rec[k]==status]
        for ls in rows+[dead]:h.update((' '.join(map(str,ls))+' 0\n').encode())
        with p.open('rb') as fd:assert h.digest()==hashlib.file_digest(fd,'sha256').digest()
        proof=p.with_suffix('.check').read_bytes()
        if '--replay' in sys.argv:
            proof=subprocess.run(['target/drat-trim/drat-trim',str(p),str(p.with_suffix('.drat'))],check=True,capture_output=True).stdout
        assert b's VERIFIED' in proof
        print(mode,tag,len(dead),h.hexdigest(),[l for l in proof.decode().splitlines() if 'resolution steps' in l])
    return rec
if __name__=='__main__':
    modes=[s for s in sys.argv[1:] if not s.startswith('--')] or ['mask','board','south','north']
    rr={s:audit(s) for s in modes}
    if 'north' in rr and 'board' not in rr:
        # The north input list is already filtered by the checked mask,
        # single-corner tables and 125 prohibition; don't sum overlaps.
        remaining=[k for k,v in rr['north'].items() if not v.startswith('VERIFIED')]
        print('corner-only ledger:',4599-len(remaining),'excluded;',len(remaining),'open;',
              len({k.split('@')[0] for k in remaining}),'open parents')
    if 'board' in rr and 'south' in rr:
        a,b=rr['board'],rr['south'];assert a.keys()==b.keys()
        survivors=[k for k in a if all(not r[k].startswith('VERIFIED') for r in (a,b))]
        tables=[]
        for label in ('local','local_remote'):
            tables.append(json.loads((OUT/f'{label}.json').read_text()))
            assert b's VERIFIED' in (OUT/f'{label}_union.check').read_bytes()
        kept=[k for k in survivors if all(local[k.split('-')[1]]!='VERIFIED' for local in tables)]
        print('additional exclusions from the single-corner projection',len(survivors)-len(kept))
        survivors=kept
        from pathlib import Path
        assert b's VERIFIED' in Path('target/offrail103_crop_3_7_size30_sig125.check').read_bytes()
        kept=[k for k in survivors if '125' not in k.split('@')[0].split('-')]
        print('additional exclusions from the signature-125 proof',len(survivors)-len(kept))
        survivors=kept
        count=Counter(k.split('@')[0] for k in survivors)
        if 'north' in rr:
            survivors=[k for k in survivors if not rr['north'][k].startswith('VERIFIED')]
            count=Counter(k.split('@')[0] for k in survivors)
        print('open site assignments',len(survivors),'of 4599;',len(count),'of 73 parents')
        print('open mask counts',Counter(k.split('@')[1] for k in survivors))
        print('eliminated parents',sorted({k.split('@')[0] for k in a}-count.keys()))
        if '--list-open' in sys.argv:print('open:',','.join(survivors))
