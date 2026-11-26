"""Replay the best measured one-row/one-column comparison to residue zero."""
import subprocess
from .dense_joint_collar import upper,marks,verify

def price(r):
    s=subprocess.check_output(['target/compress_cross'],input='\n'.join(r),text=True).splitlines()
    cost,y,x,removed,cycles,repairs,score=map(int,s[0].split())
    tree=verify(s[1:]);assert tree[0]==score==marks(r)-removed-repairs
    print('side',len(r),'cut',y,x,'deleted, nullity, actual repairs',removed,cycles,repairs,
          'parent upper',upper(len(r)-1)+removed+repairs,'tree',tree,flush=True)
    return upper(len(r)-1)+removed+repairs

if __name__=='__main__':
    from .comb_cap_transfer import construct
    from .dense_joint_collar import punctures
    from .crop_end_coupling import locked_fringe
    for name,r in [('comb',construct(103,4)),('locked',locked_fringe(103)),('double',punctures(103,True))]:
        print(name,flush=True);price(verify(r,True))
