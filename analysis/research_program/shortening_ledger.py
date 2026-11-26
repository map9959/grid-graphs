"""Disjoint certified one-gap exclusions and independent strip relation checks."""
from .depth_two_203_ledger import checked,CERTS
from .defect_window import table
from .zipper_rails import verify,build

RECT=[
    (173,[200,206,212],'3c1bc86e6c8f25fb3057cb4a2402e82473df77ed4506359622fd36b66e757eb8'),
    (197,[218,224,230,236],'a72e68315571e3d29b9901c27b71de5762afcd59ff17f2cc9814195edfb7e160')]
QUARTERS=[
    (197,233,'f7ff683f46e7ed909410dbb176687447ba81d0f6e5365fe173aaa95e1600649f'),
    (239,239,'7adb062c33c67cc025ada64d81657b38119520ccc44beb872d190676e7016d72')]
SWEEP=[
    '4ccf271f163565c8f8ad1f9512d79f30dd9e5785e54c191647824db1999f42a8',
    'bf57ffce235720bda1a11e43a841f92fa6e88bb8e0c032fd6aeb18e8b3f1698c',
    'f7bf5e6626db60657fbd41a494de3dbf7a64295306ff47b7babd22fc828dc3a7']

def run():
    ds=set(range(5,240,3))
    for _,lo,hi,name,digest in CERTS:
        checked(name,digest)
        ds-=set(range(lo,hi+1,6))
    assert len(ds)==47
    for side,new,h in RECT:
        checked(f'long_star_rectangle_{side}',h)
        assert set(new)<=ds
        ds-=set(new)
        print('s VERIFIED intact rectangle',side,'x',side+42,'excludes',new)
    for lo,hi,h in QUARTERS:
        checked(f'long_star_quarters_{lo}_{hi}',h)
        new=set(range(lo,hi+1,6));assert new<=ds;ds-=new
        print('s VERIFIED intact 102-layer bands exclude',sorted(new))
    print('unexcluded distances per arm',sorted(ds),'sites per frame',2*len(ds))
    for k,h in enumerate(SWEEP):checked(f'star_strip_5_5_1_0_sw{k}',h)
    checked('star_strip_5_5_1_0_h38','d95d1de3a8dafaf58fe828761b28e1095066bbf5d02a9bb4dd91d3a674fbd833')
    T=table(245)[0];U=table(119)[0];short=table(203)[0]
    for tag in (0,1):
        for k in range(79-2*tag):
            for r in range(2*tag,102):
                assert T(tag,150+k,244-r)==U(tag,12+k,118-r)
                for s in range(102,161):
                    assert T(tag,s+k,244-r)==short(tag,150+s%3+k%3,202-r)
    print('s VERIFIED missing 36-step mask records for all 59 starts;',
          'start 150 obstruction at width 38; clean long-strip types transplant to 119')
    print('245 rail spanning tree',verify(build(245)),'unrestricted upper',3*81**2+7*81-(81-5)//7)
if __name__=='__main__':run()
