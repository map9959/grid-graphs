"""Check both interfaces and shorten the width-seven one-gap patch obstruction."""
from itertools import product
from .joint_rim_pump import relation
from .defect_window import table,DIR,trans
from .odd_frames import frame

def run(star=False):
    L={d:(relation(7,one_gap_star=True,star_dir=d) if star else relation(7,patch_dir=d))[0] for d in (0,2)}
    assert 12+max(L.values())+2<119-8
    for n in (119,161):
        types=table(n)[0]
        for tail in product((1,3),repeat=3):
            m=frame(n,(0,*tail));todo=[(0,0)];p={(0,0):-1}
            for i,j in todo:
                for d,(a,b) in enumerate(DIR):
                    v=i+a,j+b
                    if v in m and min(*v,n-1-v[0],n-1-v[1])==0 and v not in p and (m[i,j] or m[v]):
                        p[v]=(d+2)%4;todo.append(v)
            for j in range(11,12+max(L.values())+n-119+2):
                assert p[0,j]==0 and p[j,0]==3
                assert m[0,j]==m[j,0]==1 and m[1,j]==m[j,1]==0
        for tag in (0,1):
            for r in range(7-2*tag):
                for j in range(11,12+max(L.values())+n-119+2):
                    assert types(tag,r,j)==types(tag,r,12+(j-12)%3)
        print(n,'fixed north/eastward and transposed west/backward interfaces checked')
        if star and n==161:
            assert set(L.values())=={36}
            # A second clean piece gives control of the *exact* site,
            # not just its residue, on enlargement. 108 = 161-53.
            for j in range(107,108+36+2):
                assert p[0,j]==0 and p[j,0]==3
                for tag in (0,1):
                    for r in range(7-2*tag):
                        assert types(tag,r,j)==types(tag,r,12+(j-12)%3)
            for ell in range(5,n+42-5,3):
                if ell==8:continue
                before=ell if ell<n-53 else ell-42
                assert 5<=before<=n-6 and before!=8
                assert before<n-53 if before==ell else before>=12+36
            print('second clean cut at n-53; every eligible distance except 8 lifts outside a clean piece')
if __name__=='__main__':
    import sys
    run('--star' in sys.argv)
