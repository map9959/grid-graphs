"""Partition the side-103 no-pitch floor by the exact number of straight segments."""
import argparse
from collections import Counter
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
from .integral_rank_floor import Floor,verify,physical
from itertools import product,combinations


def surplus(m):
    """B+U-T plus weighted rim vacancies less four mandatory vacancies."""
    n=m.n;z=[];rim=[]
    mandatory=[((i,j+(1 if not j else -1)),(i+(1 if not i else -1),j))
               for i,j in product((0,n-1),repeat=2)]
    fringe={site for pair in mandatory for site in pair}
    for a,b in mandatory:rim.append(m.conj([-m.X[a[0]][a[1]],-m.X[b[0]][b[1]]]))
    for i,j in product(range(n),repeat=2):
        s=m.X[i][j];nb={(u,v):m.X[u][v] for u,v in ((i-1,j),(i+1,j),(i,j-1),(i,j+1))
                         if 0<=u<n and 0<=v<n}
        if (i,j) not in fringe:rim.extend([-s]*(4-len(nb)))
        a=m.p.id();z.append(a);m.f.append([s,*nb.values(),a])
        for p,q in combinations(nb,2):
            if p[0]!=q[0] and p[1]!=q[1]:continue  # diagonal exclusion
            exc=[]
            if i%3==0 and j%3 and p[0]==q[0]:
                exc=[m.mixed[i,j+(-1 if j%3==1 else 1)]]
            if j%3==0 and i%3 and p[1]==q[1]:
                exc=[m.mixed[i+(-1 if i%3==1 else 1),j]]
            m.f.append([s,-nb[p],-nb[q],a,*exc])
    return z,rim


def thresholds(f,p,lits,limit):
    """Unary totalizer, both implications, capped at the largest queried threshold."""
    if len(lits)==1:return lits
    k=len(lits)//2
    a,b=(thresholds(f,p,v,limit) for v in (lits[:k],lits[k:]))
    c=[p.id() for _ in range(min(limit,len(a)+len(b)))]
    for i in range(len(a)+1):
        for j in range(min(len(b),len(c)-i)+1):
            s=i+j
            if s:f.append(([-a[i-1]] if i else [])+([-b[j-1]] if j else [])+[c[s-1]])
            if s<len(c):f.append(([a[i]] if i<len(a) else [])+([b[j]] if j<len(b) else [])+[-c[s]])
    return c


def run(args):
    m=Floor(103,43);cost=m.segments()
    from .physical_mark_count import add
    add(m.f,m.p,m.row_used,13)
    if args.faces:m.faces()
    if args.cut:
        from .integral_floor_cross import add_cross
        m.cross=(*args.cut,*add_cross(m,*args.cut,79))
    bins=thresholds(m.f,m.p,cost,39);rhs=None
    if args.surplus:
        from pysat.card import ITotalizer
        extra,rim=surplus(m)
        with ITotalizer(lits=extra+rim,ubound=24,top_id=m.p.top) as cnt:
            m.f.extend(cnt.cnf.clauses);rhs=cnt.rhs[:]
    counts=Counter()
    with TemporaryDirectory(prefix='segments-',dir='target') as tmp:
        path=Path(tmp);cnf=path/'in.cnf';proof=path/'proof'
        with cnf.open('wb') as f:
            f.write(f'p cnf {m.f.nv} {len(m.f.clauses)+2+int(rhs is not None)}\n'.encode())
            for c in m.f.clauses:f.write((' '.join(map(str,c))+' 0\n').encode())
            offset=f.tell()
        print('common CNF',m.f.nv,len(m.f.clauses)+2+int(rhs is not None),'clauses including branch units',flush=True)
        for s in range(args.lo,args.hi+1):
            q=s-35
            with cnf.open('r+b') as f:
                units=[bins[q-1],-bins[q]]
                if rhs is not None:units.append(-rhs[75-s])  # at most 74-T
                f.seek(offset);f.write(''.join(f'{x} 0\n' for x in units).encode());f.truncate()
            res=subprocess.run(['target/cadical/build/cadical','-t',str(args.seconds),str(cnf),str(proof)],capture_output=True)
            if res.returncode==20:
                chk=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(proof)],capture_output=True)
                assert chk.returncode==0 and b's VERIFIED' in chk.stdout
                status='UNSAT s VERIFIED'
            elif res.returncode==10:
                val={int(w) for line in res.stdout.splitlines() if line.startswith(b'v ') for w in line[2:].split()}
                board=[''.join('#' if z in val else '.' for z in row) for row in m.X]
                assert physical(board)[:3]==(43,0,1) and verify(board)[0::4]==(3647,3647)
                if args.cut:
                    from .integral_floor_cross import replay_cross
                    replay_cross(m,board,val)
                Path('analysis/research_program/forest_103_floor.txt').write_text('\n'.join(board)+'\n')
                print('segments',s,'SAT',verify(board),flush=True);return
            else:
                assert res.returncode==0 and b'UNKNOWN' in res.stdout,(res.returncode,res.stderr[-500:])
                status='UNKNOWN'
            counts[status]+=1;print('segments',s,status,flush=True)
    print('partition',args.lo,args.hi,dict(counts),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--lo',type=int,default=51);p.add_argument('--hi',type=int,default=73)
    p.add_argument('--seconds',type=int,default=15);p.add_argument('--faces',action='store_true')
    p.add_argument('--surplus',action='store_true')
    p.add_argument('--cut',nargs=2,type=int)
    args=p.parse_args();assert 51<=args.lo<=args.hi<=73 and args.seconds>0
    run(args)
