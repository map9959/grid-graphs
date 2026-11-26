"""Combine only checked two-group exclusions; verify coverage against geometry."""
from collections import Counter,defaultdict
from itertools import combinations
from pathlib import Path
import json

def summarize():
    dest=Path('target/offrail103_two8')
    eight=((2,'12'),(4,'12'),(6,'23'),(7,'23'),(8,'23'),(9,'23'),(9,'34'),(10,'23'))
    live={f'{d}:{"".join(w)}-{e}' for d,e in eight for n in range(3,7)
          for w in combinations('012345',n) if '2' in w or '2' in e}
    assert len(live)==320
    for stage,budget in (('board',500),('crop',1600),('crop2',5000),('strip',10000),('collar',12000)):
        p=dest/f'{stage}_{budget}.json'
        if not p.exists():
            assert stage=='collar';break
        results=json.loads(p.read_text())
        assert live<=results.keys()
        negatives={k for k,v in results.items() if v=='VERIFIED UNSAT'}
        if negatives:assert b's VERIFIED' in (dest/f'{stage}_union.check').read_bytes()
        live-=negatives
        print(stage,dict(Counter(results.values())),len(live),'still open')
    west=defaultdict(list)
    for k in sorted(live):
        d,m=k.split(':');w,e=m.split('-');west[int(d),e].append(w)
    for k in eight:print(*k,','.join(west[k]) or 'excluded')
if __name__=='__main__':summarize()
