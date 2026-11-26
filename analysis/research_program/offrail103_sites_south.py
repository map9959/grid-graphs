"""Price the last two site signatures in a collar rooted at the south end."""
from pathlib import Path
import subprocess,sys
from .diagonal_score import generate
from .offrail103_one_depth import band,N

def test(sec):
    # Generate in root-relative coordinates, with physical north at i=N-1.
    region={(i,j) for i in range(N) for j in range(N)
            if min(i,j,N-1-j)<15 or i>=N-21}
    f,X=generate(N,3647,region)
    def lit(v):
        i,j=divmod(v-1,N);return X[(N-1-i)*N+j]
    for d in range(6):f.append([lit(v) for v in band(0,d)])
    for v in band(0,6):f.append([-lit(v)])
    for side in (1,2,3):
        for d in range(11):f.append([lit(v) for v in band(side,d)])
    # West 123 or 0123 (leave 0 free), east exactly 23.
    for side,yes,no in [(1,(1,2,3),(4,5)),(3,(2,3),(0,1,4,5))]:
        for t in (*yes,*no):
            vs=[lit(v) for v in band(side,7) if (v-1)//N<=16 and (v-1)//N//3==t]
            if t in yes:f.append(vs)
            else:f.extend([[-v] for v in vs])
    for i in (7,8):
        for j in (94,95,96):
            x=lit(1+N*i+j);f.append([x if j==96 else -x])
    stem=Path('target/offrail103_sites/south')
    p=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat');f.to_file(str(p))
    with stem.with_suffix('.log').open('wb') as fd:
        rc=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(p),str(pr)],stdout=fd).returncode
    if rc==20:
        data=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],check=True,capture_output=True).stdout
        assert b's VERIFIED' in data;stem.with_suffix('.check').write_bytes(data)
        print('two remaining site assignments: s VERIFIED')
    elif rc==10:print('crop SAT')
    else:assert rc==0;print('UNKNOWN')
if __name__=='__main__':test(int(sys.argv[1]))
