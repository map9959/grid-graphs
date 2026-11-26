"""Two independently replayable finite strip proofs and the physical lower tree."""
from hashlib import sha256
from itertools import product
from pathlib import Path
import json,sys
from .coupled_mask_audit import audit,execute
from .coupled_mask_check import check
from .coupled_two_gap import instance
from .two_gap_mask_tables import VERIFIED
from .tile_case_ledger import check_types,digest
from .zipper_rails import build,verify

def main():
    n=623;k=(n-2)//3
    check_types(n)
    p=Path('target/tile_catalogue_proofs')
    manifest=json.loads((p/'manifest_0_12.json').read_text())
    assert digest(Path('target/tile_family_3_5_h6.json.gz'))==manifest['catalogue']
    assert {tuple(uv) for uv,*_ in manifest['proofs']}==set(product(range(13),repeat=2))
    for (u,v),_,_,h in manifest['proofs']:assert digest(p/f'word_{u}_{v}.drat')==h
    audit()
    cover=[(1,1,103),(1,104,154),(1,155,205),(2,1,205)]
    assert all([q for ax,l,h in cover if ax==a for q in range(l,h+1)]==list(range(1,k-1)) for a in (1,2))
    for ax,l,h in cover:assert check(ax,k,(l,h))
    exits=[d for d in range(5,n-5,3) if min(d,n-1-d)>=308]
    assert exits==[308,311,314]
    for e in exits:
        q=(e-2)//3
        data=instance(k,q,drat='--drat' in sys.argv)
        ans=execute(data,q=q);assert ans==f'EMPTY h=3 pass=0 horizontal=false start={q-1}'
        assert check(1,k,('ordinary exit',e),data=data,q=q)
        print(e,'grid sha256',sha256(data.encode()).hexdigest(),ans,flush=True)
    if '--drat' in sys.argv:print('fresh local drat-trim cover checks:',len(VERIFIED))
    U=3*k*k+7*k-(k-5)//7
    result=verify(build(n))
    assert result==(U-1,n*n-2,2,n*n-1,U-1)
    print('physical rail replay:',result,'P(623,623) =',U-1)
if __name__=='__main__':main()
