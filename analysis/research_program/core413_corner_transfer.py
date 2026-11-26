"""Compare the checked NW models after enlargement, including every face owner."""
import hashlib,sys
from .two_gap_exit_box import test

def signature(n,width,height,d,lo,hi):
    old=sys.argv[:]
    sys.argv=['box','--axis=1',f'--side={n}']
    result=[]
    def audit(f,axis,flags,bit,dom,exits,charged):
        assert charged and exits==list(range(lo,hi+1,3))
        # Only unused global row/column flags depend in number on n.
        # Remove their implications, and relabel all other flags by their
        # fixed box-relative tile centers. Keep every other clause and sign.
        K=len(flags);ref=len(range(14,413-14,3));sv=axis+2*K
        ids=list(range(f.nv+1));unused=set()
        for z,i in flags.items():
            if i+1>=height:unused.add(z)
            if i+1>=width:unused.add(z+K)
            ids[z+K]=z+ref
        for v in range(sv+1,f.nv+1):ids[v]-=2*(K-ref)
        digest=hashlib.sha256();raw=hashlib.sha256()
        raw.update(f'p cnf {f.nv} {len(f.clauses)}\n'.encode())
        for c in f.clauses:
            line=(' '.join(map(str,c))+' 0\n').encode();raw.update(line)
            if len(c)==2 and c[0]<0 and -c[0] in unused and abs(c[1])==axis:continue
            if any(v>axis or v< -axis for v in c):
                assert not any(abs(v) in unused for v in c)
                line=(' '.join(str(ids[v] if v>0 else -ids[-v]) for v in c)+' 0\n').encode()
            digest.update(line)
        print(n,width,'normalized',digest.hexdigest(),'raw',raw.hexdigest(),flush=True)
        result.append((digest.hexdigest(),raw.hexdigest()))
    try:test(width,height,d,'left',0,merge=audit,distances=list(range(lo,hi+1,3)))
    finally:sys.argv=old
    return result[0]

if __name__=='__main__':
    for spec,expected in [
        ((270,99,155,107,200),'8768834ee23f064abceae9c096752c124d74f56cf37e4720b60db6c68ebfd89a'),
        ((373,114,251,203,305),'08acb26b563487cde76a3e164b68c44f3ce86f888a7f2d6f147de98729d13b85')]:
        base,raw=signature(413,*spec);assert raw==expected
        assert signature(455,*spec)[0]==base
