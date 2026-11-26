"""Serialize the nonzero-dual rows, with their unweighted column coefficients.

Digits are little-endian base 32, ASCII 48..111; bit 5 means continuation.
All signed fields are zigzag-coded. Rows retain their source indices; column
order is the original physical atom dictionary order, including fixed atoms.
"""
import math
from collections import defaultdict
from .free_width_dual import chart, Q, Path, json
from .face_column_keys import descriptors

DEST=Path(__file__).resolve().parents[2]/'lean/GridGraphs/NoPitch/Data'

def export(n,source,tail):
    ns,A,b,M,bo=chart(n)
    y=json.loads(Path(__file__).with_name(f'free_width_{source}.json').read_text())
    vals=[Q(v) for _,v in y]
    scale=math.lcm(*(v.denominator for v in vals))
    bs=[b]
    for m in ([n+6,n+12] if tail else []):
        ns1,A1,b1,M1,bo1=chart(m)
        assert (ns1,M1,bo1)==(ns,M,bo) and len(A1)==len(A)
        assert all((dict(A[i][0]),A[i][1])==(dict(A1[i][0]),A1[i][1]) for i,_ in y)
        bs.append(b1)
    data=bytearray()
    def u(x):
        assert x>=0
        while x>=32:
            data.append(80+x%32);x//=32
        data.append(48+x)
    def s(x):u(2*x if x>=0 else -2*x-1)
    u(scale);u(len(y));u(len(ns))
    cols=defaultdict(list)
    for j,((i,_),v) in enumerate(zip(y,vals)):
        row,op=A[i]
        u(i);u({'=':0,'<=':1,'>=':2}[op]);s(int(v*scale))
        dd=bs[2][i]-2*bs[1][i]+b[i] if tail else 0
        for coef in (2*b[i],2*(bs[1][i]-b[i])-dd if tail else 0,dd):s(coef)
        for x,c in row:
            if c:cols[x].append((j,c))
    for x,(key,units) in zip(ns.values(),descriptors(n,ns,M),strict=True):
        u(key);u(units)
        u(int(x in bo));s(M.get(x,0));u(len(cols[x]));prev=0
        for j,c in cols[x]:
            u(j-prev);s(c);prev=j
    DEST.mkdir(exist_ok=True,parents=True)
    (DEST/f'chart{n}.v32').write_bytes(data+b'\n')
    print(n,len(ns),len(y),len(data),scale,flush=True)

if __name__=='__main__':
    for n,src in [(58,106),(61,103),(19,19),(22,22),(25,25),(52,52)]:export(n,src,n>=58)
