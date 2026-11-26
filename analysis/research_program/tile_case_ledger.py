"""Replay spatial transplantation and the two-stage side-245 tile certificates."""
from itertools import product
from pathlib import Path
from hashlib import sha256,file_digest
import json,gzip,sys,subprocess
from .tile_family_lp import typ
from .slit_star_transfer import frame_path

def check_types(n=245):
    k=(n-2)//3-1;ref=119;K=38
    reps={typ(i,K):i for i in range(K)}
    def axis(x,S,h):return x if x<h else 2*h+3+x-S if x>=S-h else h+(x-h)%3
    def sig(x,N):
        return tuple(None if not 0<=x<N-2*t else (axis(x,N-2*t,6-t),axis(N-2*t-1-x,N-2*t,6-t)) for t in (0,1))
    for i in range(k):
        p=reps[typ(i,k)]
        for z in range(-7,14):
            assert sig(1+3*i+z,n)==sig(1+3*p+z,ref)
    M,A=frame_path(n,3);m,a=frame_path(ref,3)
    # Check physical frame/parent words even in the halos of off-center
    # windows. The same axis comparisons give all eight stencil images.
    for i,j in product(range(k),repeat=2):
        if min(i,j,k-1-i,k-1-j)>2:continue
        u,v=reps[typ(i,k)],reps[typ(j,k)]
        for dx,dy in product(range(-6,12),repeat=2):
            p=1+3*i+dx,1+3*j+dy;q=1+3*u+dx,1+3*v+dy
            assert M.get(p)==m.get(q) and A.get(p)==a.get(q)
    print(n,'physical stencil, frame and rooting all transfer from 119')

def digest(p):
    with p.open('rb') as f:return file_digest(f,'sha256').hexdigest()

def check():
    check_types();root=Path('target');proofs=root/'tile_catalogue_proofs'
    manifest=json.loads((proofs/'manifest_0_12.json').read_text())
    assert digest(root/'tile_family_3_5_h6.json.gz')==manifest['catalogue']
    ks=set()
    for (u,v),num,cnf,proof in manifest['proofs']:
        assert digest(proofs/f'word_{u}_{v}.drat')==proof;ks.add((u,v))
    assert ks==set(product(range(13),repeat=2))
    # The second-stage CNFs use the post-catalogue seam-support sets.
    for axis in (1,2):
        stem=root/f'physical_tile_245_{axis}_5_colors2'
        assert digest(stem.with_suffix('.cnf'))=='a0e946696960573e8b55139c7ef43935a5baef49f57d0fbd6783ce09530e9538'
        assert 's VERIFIED' in stem.with_suffix('.check').read_text()
    print('169 certified mask catalogues; d=5 excluded in both axes without any prescribed interior port')
    more=root/'tile_star_catalogues';files=list(more.glob('*.json.gz'))
    for f in files:
        checkfile=f.with_suffix('').with_suffix('.check');_,ok,_,h=checkfile.read_text().split()
        assert ok=='VERIFIED' and digest(f)==h
    print(len(files),'additional flat/edge templates independently certified')
    tested={1:set(),2:set()}
    for axis,lo,hi,h in (
        (2,5,191,'cfc5796e38b17634d30bdbc8aac0a108153a82b22a19af3a6a3cdec0a489344d'),
        (1,5,95,'62580970bb35ba4ca6eae234953dd1c4124932b1c63d12616145ebd30b2b8a37'),
        (1,101,155,'2e198b6f4bad26f8f7834843f7f84c1e7f5cf1aee89ef474f89abe604be93265'),
        (1,161,167,'a7cf63ad68977c6e7dc013665c7553649a3a0b0e54e284440431db2edfcd4bc8')):
        stem=root/f'physical_tile_245_{axis}_{lo}to{hi}_colors2'
        assert digest(stem.with_suffix('.cnf'))==h and 's VERIFIED' in stem.with_suffix('.check').read_text()
        tested[axis].update(range(lo,hi+1,6))
    for lo,tag,h in ((173,'area2','b3f1a1fbe4350e311fb8e5203142981a3ed343c1ca01320e833a69d55c744c9f'),
                     (161,'flow_dual1','8130a7ccb5c0c494fc02d9d4487d553d251d077b416b7786c9eb980006a44935')):
        stem=root/f'physical_tile_245_1_{lo}to191_colors2_{tag}'
        assert digest(stem.with_suffix('.cnf'))==h and 's VERIFIED' in stem.with_suffix('.check').read_text()
        tested[1].update(range(lo,192,6))
    assert all(v==set(range(5,192,6)) for v in tested.values())
    two=root/'two_gap_245_all_axis.cnf'
    assert digest(two)=='e90425d26efe7913bbf115ccf2e127a677c8a0595fa6e486f46f7692e6b3f44d'
    assert 's VERIFIED' in two.with_suffix('.compactcheck').read_text()
    from .shortening_ledger import run
    run()
    from .zipper_rails import verify,build
    assert verify(build(245))==(20239,60023,2,60024,20239)
    print('both gap counts exhausted; P(245,245) = 20239')
if __name__=='__main__':check()
