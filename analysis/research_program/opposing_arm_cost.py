"""Donor-free corollaries of the western transfer, allowing any north star."""
from .western_cut_transfer import BT,coupled,north_star_union
from .fringe_suffix_bound import check as plateau

def check():
    plateau(north_star_union(),True)
    edge={(c,d) for a,b,c,d in BT[6,6]}
    pairs={(x,y) for x,y in edge if x!=7 and y!=448 and (7,x) in edge and (y,448) in edge}
    short=set()
    def walk(w,left):
        if w[-1]==448:short.add(w[1:-1])
        for a,b in edge:
            # Collapse consecutive identical full tiles, charging all
            # other steps their true loss, including deficient self-loops.
            if a==w[-1] and (a!=b or b.bit_count()!=3) and 3-b.bit_count()<=left:
                walk(w+(b,),left-3+b.bit_count())
    walk((7,),3)
    assert len(short)==14 and pairs=={(3,24),(16,16),(33,24),(48,24),(48,264)}
    for axis in (1,2):
        for s in (13,14,15,16):
            survive=[]
            for m in sorted(pairs):
                args=dict(middle=m,all_stars=True,long_prefix=s==16)
                if coupled(axis,s,7,0,**args):survive.append(m)
                assert coupled(axis,s,7,0,break_from=s-7,**args)==0
            assert survive==[(16,16)]
        for m in short:
            assert not any(v.bit_count()==3 and v!=56 for v in m)
            args=dict(all_stars=True,long_prefix=True)
            assert not coupled(axis,13,7,0,middle=m,**args)
            if 56 in m:
                assert m.index(56)==1 and len(m)==3
                assert not coupled(axis,13,7,0,middle=(m[0],56,56,m[-1]),repeat_middle=True,**args)
        print('axis',axis,': only (16,16) survives two-tile test; all 14 cheap skeletons excluded')
if __name__=='__main__':check()
