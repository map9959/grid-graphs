"""Can an intact 245 charged rectangle be shortened along the star arm only?"""
from itertools import product
from pathlib import Path
import gzip,sys
from .depth_two_far_quarter import run
from .shorten_245_star import audit
from .depth_two_203_ledger import boundary,CERTS,checked
from .defect_window import table,DIR

def test(which,seconds):
    side,lo,hi,name,digest=CERTS[which]
    checked(name,digest)
    ds=[d+42 for d in range(lo,hi+1,6) if d+42>194]
    assert ds
    # The two exterior arm labels may be interchanged by transposition.
    # Transverse rows are *not* lengthened: the 203 proof never needed
    # the south perimeter here. Both rectangles have identical near
    # types off the insert and the far longitudinal end translates by 42.
    A=set(product(range(side),range(side+42)))
    archive=Path(__file__).with_name('one_gap_projection_examples')/f'long_rectangle_{side}.gz'
    def replay(w,star,X,out):
        word=list(product((1,3),repeat=3))[w%8]
        m,p=boundary(245,word)
        if w>=8:
            m={(j,i):v for (i,j),v in m.items()}
            p={(j,i):((1-d)%4 if d>=0 else -1) for (i,j),d in p.items()}
        v,e,cc=audit(245,A,X,out,star,None,table(245),(m,p))
        assert star[1] in ds and lo<=star[1]-42<=hi
        print('unbroken rectangle',side,'by',side+42,'star',star,'frame',w,'vertices',v,'edges',e,
              'components',len(set(cc.values())),'cycles 0; short square',side,'by',side,'s VERIFIED',flush=True)
        if not archive.exists():
            raw=bytes([w,star[1]])+bytes(5*int(u in X)+out.get(u,-1)+1 for u in sorted(A))
            archive.write_bytes(gzip.compress(raw,mtime=0))
    if seconds==-1:
        raw=gzip.decompress(archive.read_bytes());data=dict(zip(sorted(A),raw[2:],strict=True))
        replay(raw[0],(2,raw[1]),{u for u,b in data.items() if b>=5},{u:b%5-1 for u,b in data.items() if b%5})
    else:
        run(245,min(ds),max(ds),seconds,domain=A,distances=ds,output=f'target/long_star_rectangle_{side}',
            root_site=(0,0),replay=replay)
if __name__=='__main__':test(*map(int,sys.argv[1:]))
