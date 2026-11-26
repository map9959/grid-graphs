"""Compare physical two-corner charge models under an 18-side enlargement."""
from hashlib import sha256
from .diagonal_score import generate

def signature(n,larger=False,single=None,remote=False):
    dom={(i,y) for i in range(30) for j in range(30) if i<=14 or j<=11 or (larger and max(i,j)<24) for y in (j,n-1-j)}
    if single is not None:dom={(n-1-i if remote else i,j) for i in range(30) for j in range(30) if i<=single+4 or j<=11}
    k=n//3
    f,X=generate(n,3*k*k+(16*k-7)//3,dom)
    # Give corresponding mark sites common names, preserving handedness;
    # the remaining variables may be renamed by first occurrence.
    ids={X[n*i+j]:1+i*60+(j if j<30 else 60+j-n) for i,j in dom}
    if single is not None:ids={X[n*i+j]:1+30*(n-1-i if remote else i)+j for i,j in dom}
    counter=1800;h=sha256()
    for c in f.clauses:
        row=[]
        for x in c:
            a=abs(x)
            if a not in ids:counter+=1;ids[a]=counter
            row.append(ids[a] if x>0 else -ids[a])
        h.update((str(row)+'\n').encode())
    return len(dom),len(f.clauses),h.hexdigest()
if __name__=='__main__':
    import sys
    base=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--side=')),103)
    depth=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--single=')),None)
    opts=('--refine' in sys.argv,depth,'--remote-root' in sys.argv)
    ref=signature(base,*opts);print(base,ref,flush=True)
    nxt=signature(base+18,*opts);print(base+18,nxt,flush=True)
    assert ref==nxt
