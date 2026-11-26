"""Read proof CNFs: recover physical group masks and compare labelled unions."""
from pathlib import Path
from collections import Counter,deque
import hashlib,json,subprocess,sys
from .offrail103_joint_summary import report
from .offrail103_one_depth import N

def audit():
    dest=Path('target/offrail103_joint_south')
    for d,pairs in report().items():
        record=json.loads((dest/f'd{d}.json').read_text());labels=['-'.join(p) for p in pairs]
        assert set(labels)==set(record)
        for status in sorted(set(record.values())):
            if not status.startswith('VERIFIED '):continue
            stem=dest/f"d{d}_{status.split()[1]}";p=stem.with_suffix('.cnf')
            proof=stem.with_suffix('.check').read_bytes()
            assert b's VERIFIED' in proof
            if '--replay' in sys.argv:
                proof=subprocess.run(['target/drat-trim/drat-trim',str(p),str(stem.with_suffix('.drat'))],capture_output=True,check=True).stdout
                assert b's VERIFIED' in proof
            groups=[]
            for cols in (range(6,9),range(N-9,N-6)):
                for t in range(6):
                    groups.append({1+N*(N-1-i)+j for i in range(17) if i%3 and i//3==t for j in cols})
            def physical_band(side,t):
                sites=set()
                for u in range(max(0,t-1),t+2):
                    for j in range(N):
                        if j%3==0:continue
                        i,k=((u,j),(j,u),(N-1-u,j),(j,N-1-u))[side]
                        sites.add(1+N*(N-1-i)+k)
                return sites
            with p.open('rb') as fd:
                _,_,v,c=fd.readline().split();v=int(v);c=int(c)
                # Last group definitions and selectors have no intervening
                # auxiliary variables. Check signs, east/west and reflection.
                size=sum(len(g)+1 for g in groups)+12*len(labels)+1+d+len(physical_band(0,d))+33
                tail=deque(fd,maxlen=size)
            rows=iter(list(map(int,line.split()[:-1])) for line in tail)
            for t in range(d):assert set(next(rows))==physical_band(0,t)
            assert {tuple(next(rows)) for _ in physical_band(0,d)}=={(-v,) for v in physical_band(0,d)}
            for side in (1,2,3):
                for t in range(11):assert set(next(rows))==physical_band(side,t)
            z0=v-len(labels)-12
            for i,g in enumerate(groups,1):
                z=z0+i;cl=next(rows);assert cl[0]==-z and set(cl[1:])==g
                assert {tuple(next(rows)) for _ in g}=={(-x,z) for x in g}
            excluded=[]
            for t,label in enumerate(labels,1):
                z=z0+12+t
                w,e=label.split('-')
                for i in range(12):
                    g=z0+1+i;assert next(rows)==[-z,g if str(i%6) in (w,e)[i//6] else -g]
                if record[label]==status:excluded.append(z)
            assert next(rows)==excluded and next(rows,None) is None
            with p.open('rb') as fd:h=hashlib.file_digest(fd,'sha256').hexdigest()
            print('audited',d,len(excluded),h)
        live=[p for p in pairs if not record['-'.join(p)].startswith('VERIFIED ')]
        label='omit2' if d==3 else '0134'
        stem=dest/f'd{d}_only_{label}'
        pr=stem.with_suffix('.check').read_bytes()
        assert b's VERIFIED' in pr
        if '--replay' in sys.argv:
            data=subprocess.run(['target/drat-trim/drat-trim',str(stem.with_suffix('.cnf')),str(stem.with_suffix('.drat'))],check=True,capture_output=True).stdout
            assert b's VERIFIED' in data
        bad=lambda m: '2' not in m if d==3 else m=='0134'
        extra=[p for p in live if any(bad(m) for m in p)]
        live=[p for p in live if p not in extra]
        print('depth',d,Counter(record.values()),'extra from reflected one-corner proof',len(extra),'remaining',len(live))
        print('remaining signatures',sorted({m for p in live for m in p}))
        if '--list-open' in sys.argv:print('open',d,','.join('-'.join(p) for p in live))
        if live:
            print('surviving pairs by occupied groups',dict(sorted(Counter(len(a)+len(b) for a,b in live).items())))
            print('mandatory groups at each end',sorted(set.intersection(*(set(m) for p in live for m in p))))
            print('mandatory groups across the two ends',sorted(set.intersection(*(set(a+b) for a,b in live))))
if __name__=='__main__':audit()
