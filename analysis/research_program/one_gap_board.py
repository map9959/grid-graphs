"""Test all eight one-gap frames in one full-board, proof-producing solve."""
from .one_gap_rim import frame, DIR, product
from .defect_window import table, window
from .extend_forest_28 import verify
from pathlib import Path
from hashlib import sha256
import subprocess, sys

def run(n, seconds, phase=-1):
    assert n>=119 and (n-35)%42==0
    words=[(0,)+w for w in product((1,3),repeat=3)]
    frames=[frame(n,w) for w in words]
    boundary={(i,j) for i,j in frames[0] if min(i,j,n-1-i,n-1-j)==0}
    path={(0,0):-1};order=[(0,0)]
    for i,j in order:
        for d,(a,b) in enumerate(DIR):
            v=i+a,j+b
            if v not in boundary:continue
            forced=[bool(m[i,j] or m[v]) for m in frames]
            assert len(set(forced))==1
            if forced[0] and v not in path:path[v]=(d+2)%4;order.append(v)
    assert len(path)==4*n-4
    def emit(f,bit,flags):
        for (kind,i,j),v in flags.items():
            if kind=='s' and (i,j) in boundary:f.append([-v])
        # Each closed corner has either 0111 or 1101, independently.
        # Encode their disjunction by eight selectors; shared literals
        # are unit clauses to aid proof replay.
        sels=list(range(f.nv+1,f.nv+1+len(frames)));f.append(sels)
        for u in frames[0]:
            z=bit(*u);ls=[z if m[u] else -z for m in frames]
            if len(set(ls))==1:f.append([ls[0]])
            else:
                for s,lit in zip(sels,ls):f.append([-s,lit])
        stem=Path(f'target/one_gap_board_{n}'+(f'_phase{phase}' if phase!=-1 else ''))
        cnf=stem.with_suffix('.cnf');proof=stem.with_suffix('.drat')
        f.to_file(str(cnf))
        print('full board',n,'frames',len(words),'perimeter arrows including root',len(path),
              'variables',f.nv,'clauses',len(f.clauses),'CNF',sha256(cnf.read_bytes()).hexdigest(),flush=True)
        f.clauses.clear()
        log=stem.with_suffix('.log')
        with log.open('w') as out:
            result=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(cnf),str(proof)],stdout=out)
        if result.returncode==20:
            check=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(proof)],capture_output=True)
            stem.with_suffix('.check').write_bytes(check.stdout)
            assert check.returncode==0 and b's VERIFIED' in check.stdout
            print('all eight one-gap frames excluded: s VERIFIED',flush=True)
        elif result.returncode==10:
            chosen={int(x) for l in log.read_text().splitlines() if l.startswith('v ') for x in l[2:].split()}
            rows=[''.join('#' if bit(i,j) in chosen else '.' for j in range(n)) for i in range(n)]
            values=verify(rows);k=(n-2)//3;assert values[0]==values[-1]==3*k*k+7*k-(k-5)//7
            stem.with_suffix('.forest').write_text('\n'.join(rows)+'\n');print('forest verified',values)
        else:print('no decision',result.returncode,flush=True)
        if result.returncode!=20 or check.returncode==0:proof.unlink(missing_ok=True)
    if phase==-1:
        window(n,'rim',n,table(n),matching=True,orient=path,emit=emit)
    else:
        assert phase in (2,5);T=table(n)
        sites={('s',i,j) for d in range(5,n-5,3) if d%6==phase for i,j in ((2,d),(d,2))}
        def tight(f,bit,flags,arc,sheet):
            assert set(flags)==sites
            # A marked depth-two tooth points straight out to its unique
            # marked frame foot. Include the forbidden bulk joins directly.
            dep=lambda i,j:min(i,j,n-1-i,n-1-j)
            typ,_,charge=T;ds=tuple(range(4))
            for i,j in product(range(2,n-2),repeat=2):
                layer=dep(i,j)
                for d,(a,b) in enumerate(DIR):
                    x,y=i+2*a,j+2*b;l=dep(x,y)
                    if layer==2 and not l:f.append([-bit(i,j),-bit(x,y),arc(i,j,d)])
                    if d>=2 or l<2:continue
                    if not(layer>2 and charge(typ(0,i,j),ds,d,False,False)[1]==0 or
                           l>2 and charge(typ(0,x,y),ds,d+2,False,False)[1]==0):
                        f.append([-bit(i,j),bit(i+a,j+b),-bit(x,y)])
            emit(f,bit,flags)
        window(n,'rim',n,T,matching=True,orient=path,emit_graph=tight,defects=sites,outward_completion=True)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
