"""Side 287: audit both defect cases, physical star windows and finite cover."""
from itertools import product
import json,subprocess,sys
from pathlib import Path
from .tile_case_ledger import check_types,digest
from .tile_family_lp import typ
from .zipper_rails import build,verify

PROOFS=[
    ('two_gap_287_all_axis','65b8699338765af0b4b8481d77a77d6b610be05a2a34c92aa36807bbbb57dc32'),
    ('physical_tile_287_2_5to281_bothphase_colors2','0e0f1d5662b11f6ba80782dbf8f6716acd6da645e1aa8c1f0b34396bc7aa6afd'),
    ('physical_tile_287_1_5to143_bothphase_colors2','7f45324fb0040c1e3ed012d9a4f78e9fa2e26b4c26dceeb2a9b308df773219ae'),
    ('physical_tile_287_1_146to281_bothphase_colors2_area2','09365d099a9a2e345243d2c31b27f6578f4b7429652afd4e2274bcc9e6252c78')]

PROOFS329=[
    ('two_gap_329_0011_axis_ordinary','737e630719ba69df981a07283d24397617f4e07359a33cf61c78d7d60d6cce44'),
    ('physical_tile_329_2_5to323_bothphase_colors2','903139bf87872dd82dc9b2b0a1a0f11c7f6c5b85af56492967e881e96d9bd20a'),
    ('physical_tile_329_1_5to164_bothphase_colors2','49a7474e1780ef393a714ba327aca19d2f50ec0f561b70c541f8945f1942d07b'),
    ('physical_tile_329_1_167to242_bothphase_colors2_area2','df5789ed268f01d10c7d708703050e4c8aa0bb715856afd28aec8cdfa553dcc9'),
    ('physical_tile_329_1_245to323_bothphase_colors2_area2','44c5474276620135d216bf56f2cb6ef8647f3bc32c3da5d525615dc2cda69330')]

PROOFS371=[
    ('two_gap_371_0011_axis_ordinary_linked','61d49994f711af25fd4b84e44d0adc454ebb3c8d1604de26ff1445ec92197bb6'),
    ('physical_tile_371_2_5to365_bothphase_colors2','6ff4330d6ceb31c2cd6e64147d812e45e8939a705596fdfd1c461ba0f87e5d61'),
    ('physical_tile_371_1_5to185_bothphase_colors2','2e40371a4de7993ee36fbda3518759fc2e39a58cefef00576307302cd821f460'),
    ('physical_tile_371_1_188to275_bothphase_colors2_area2','1c27b0b0e8528d27a7864e69b43ac9ad24d58e3b8424af576025518a62b61773'),
    ('physical_tile_371_1_278to320_bothphase_colors2_area2','541543e3a961d59f94b9e77f4b27f96e3bde8579e5dd53fa4447228429611f58'),
    ('physical_tile_371_1_323to365_bothphase_colors2_area2','cb5b0fd3d0df1f095a67cd3e2e3be1e3577f0fad3102553e3c62006dc376bc9f')]

PROOFS413=[
    ('core371_lift/halo_1','7a6193ca8354d8b3fd11f40fea27351d74bff0e34596714b3c5409d141bc46f6'),
    ('physical_tile_413_2_5to407_bothphase_colors2','6f4a4ecc31a4527a43489e3815b6f874c80497fc6c7762c40933f340e7496f14'),
    ('physical_tile_413_1_5to206_bothphase_colors2','939de6354fdba1685eb3ecec6bf2b679f7bcb34847330366ba7c60524416b367'),
    ('physical_tile_413_1_209to302_bothphase_colors2_area2','9b0c60f08a50c94d0f774409fec4f3e25855537c8f2c205b3334d6ef0400da5a'),
    ('physical_tile_413_1_305to353_bothphase_colors2_area2','487526b875170ffc412d39cf277ef5cbaf71f0e0d7d971714e6e1d1d34c79ad5'),
    ('physical_tile_413_1_356to407_bothphase_colors2_area2','4c225dc8fe9af88ee513987bd891996f475ae8875a7e8950c8982d747f4d53df')]

PROOFS455=[
    ('physical_tile_455_2_5to449_bothphase_colors2','a8213bf449cf2aacb433f6d3012f32b6072534396d10e1945f50229aac86225d'),
    ('physical_tile_455_1_5to227_bothphase_colors2','dd2f795f63b2c0a23402d6cb8735f11b2b0a4a926ef60108ac380478f41079fb'),
    ('physical_tile_455_1_230to338_bothphase_colors2_area2','682cc538051f821e10841f6a7dc63a59068f5f1a980d3148ce0f5eff09a9e190'),
    ('physical_tile_455_1_341to392_bothphase_colors2_area2','c28030c6ca3f7d255ee43a2b42e8394b5d97f60a4ae896b425b432143f593ea1'),
    ('physical_tile_455_1_395to449_bothphase_colors2_area2','39a7d10e9f400931e0d54e5dd1ec9b383419ecf7c953456287a8b032e84b9998')]

PROOFS497=[
    ('physical_tile_497_2_5to491_bothphase_colors2','2f030b54d1c7caf42a23ddd630aecefcdc291e288cfffafd3c95f55b90548927'),
    ('physical_tile_497_1_5to248_bothphase_colors2','4b9266c96f8959fcc6d7d9f7904a87671cc77c76ee1116e7083384df1d6ace9a'),
    ('physical_tile_497_1_251to371_bothphase_colors2_area2','d157631a8a4b53b7d8aca2d79a93b5dd6c422a9a6ef3997663f2e2262e9454d2'),
    ('physical_tile_497_1_374to431_bothphase_colors2_area2','b0d95b9837ef14c3aff81433de1d17528fea90a33a29c3d9d3c2fba5e3ec8086'),
    ('physical_tile_497_1_434to491_bothphase_colors2_area2','30dcc71803594aae74e14183277a06a9211e06dea27edcb5b2d08fcfd92e535c')]

PROOFS539=[
    ('physical_tile_539_2_5to533_bothphase_colors2','09580a47b5a1d3790cdddb7303ca02d9fe708c33ee573005a6313a82933ef60b'),
    ('physical_tile_539_1_5to269_bothphase_colors2','bd217e21ffff8d1ce54879ddf0685e18458185b1ffef014e5064635e86c3bb75'),
    ('physical_tile_539_1_272to401_bothphase_colors2_area2','bd03f4d6f942fff00d2fdc06539527549bbd59aa1671fb8d28c7ce81f008fc3d'),
    ('physical_tile_539_1_404to467_bothphase_colors2_area2','9841e8c875eeb6c1e153b8cd1514d29bd5d76ec4ae0693e3a2228b4058b3b4cd'),
    ('physical_tile_539_1_470to533_bothphase_colors2_area2','c1a0ad604ccc65b6b24fd7fb7b1a302b7fff5c15c369d3d0d7e9d917e3773e57')]

PROOFS581=[
    ('physical_tile_581_2_5to575_bothphase_colors2','72f6c1b9ee0903b5ceec56034fa9d2afb3b6c42d6662fad12aac4e187d2e9381'),
    ('physical_tile_581_1_5to290_bothphase_colors2','cec677d03ef10e40cab9bde22d8039513db20b74beeca6edf9b06800cea00f4a'),
    ('physical_tile_581_1_293to434_bothphase_colors2_area2','7f641800d6d6d50e7f7be114c19d83460f368186dd62e381f35dc47a52f270f4'),
    ('physical_tile_581_1_437to503_bothphase_colors2_area2','5bbd7227a5e2017562b1b82e2d34c0dc5f035d9894969b23b008ab030fb11f4c'),
    ('physical_tile_581_1_506to575_bothphase_colors2_area2','bcf34d96068e81587360eadc618f4e45a49583c1c122beedf5be7302628f655a')]

def check():
    n=next((n for n in (581,539,497,455,413,371,329) if f'--{n}' in sys.argv),287)
    k=(n-2)//3;U=3*k*k+7*k-(k-5)//7
    assert (k,U,8*n//7-2)=={581:(193,113072,662),539:(179,97352,614),497:(165,82808,566),455:(151,69440,518),413:(137,57248,470),371:(123,46232,422),329:(109,36392,374),287:(95,27728,326)}[n]
    if n in (455,497,539,581):
        # By the uniform 413 end exclusions both corner distances are >=308.
        assert not [d for d in range(107,n-107,3) if min(d,n-1-d)>=308]
    if n==413:
        from .core371_lift_audit import audit
        audit()
    check_types(n)
    root=Path('target');base=root/'tile_catalogue_proofs'
    mf=json.loads((base/'manifest_0_12.json').read_text())
    assert digest(root/'tile_family_3_5_h6.json.gz')==mf['catalogue']
    kinds=set()
    for (u,v),_,_,h in mf['proofs']:
        assert digest(base/f'word_{u}_{v}.drat')==h;kinds.add((u,v))
    assert kinds==set(product(range(13),repeat=2))
    ds=range(5,n-5,3)
    proofs={287:PROOFS,329:PROOFS329,371:PROOFS371,413:PROOFS413,455:PROOFS455,497:PROOFS497,539:PROOFS539,581:PROOFS581}[n]
    for axis in (1,2):
        cover=[]
        for name,_ in proofs:
            if not name.startswith(f'physical_tile_{n}_{axis}_'):continue
            lo,hi=map(int,name.split('_')[4].split('to'))
            assert '_bothphase_' in name;cover.extend(range(lo,hi+1,3))
        assert sorted(cover)==list(ds)
    reps={typ(i,38):i for i in range(38)};extra=set()
    for i,j in product(range(k-1),repeat=2):
        u,v=typ(i,k-1),typ(j,k-1);x,y=1+3*i,1+3*j
        X,Y=1+3*reps[u],1+3*reps[v]
        for d in ds:
            # Actual rectangular halo contains the center and four neighbours.
            contains=(x-6<=1 and 3<x+12 and y-6<=d-1 and d+1<y+12)
            phase=d-y if contains else None
            assert phase==(d-y if i<=2 and -5<=d-y<=10 else None)
            old=5-Y if X-6<=1 and 3<X+12 and Y-6<=4 and 6<Y+12 else None
            if phase!=old:extra.add((u,v,phase))
    for u,v,phase in extra:
        st=root/'tile_star_catalogues'/f'word_{u}_{v}_{phase}'
        a,b,_,h=st.with_suffix('.check').read_text().split()
        assert (a,b)==('s','VERIFIED') and digest(st.with_suffix('.json.gz'))==h
    print('catalogues:',len(kinds),'base and',len(extra),'additional certified templates;',len(ds),'physical north-star distances per axis')
    for name,h in proofs:
        p=root/(name+'.cnf');assert digest(p)==h
        data=p.with_suffix('.check').read_bytes()
        if '--drat' in sys.argv:
            data=subprocess.run(['target/drat-trim/drat-trim',str(p),str(p.with_suffix('.drat'))],capture_output=True,check=True).stdout
        assert b's VERIFIED' in data;print(name,[l for l in data.decode().splitlines() if 'resolution steps' in l or 's VERIFIED' in l])
    replay=verify(build(n));assert replay==(U-1,n*n-2,2,n*n-1,U-1)
    print('physical rail tree',replay,f'P({n},{n}) =',U-1)
if __name__=='__main__':check()
