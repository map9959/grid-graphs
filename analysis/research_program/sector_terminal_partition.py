"""Exact presence/absence of a balanced terminal cut, not just a permission bit."""
import hashlib,json,shutil,subprocess,sys
from collections import Counter
from itertools import combinations
from pathlib import Path
from . import sector_survivor_tree as old
from .sector_third_split import orbit
from .extend_forest_28 import verify

dest=Path('target/sector_terminal');n=109
modes=('TB','LR','NONE');basevars=2533128
modevar={m:basevars+i for i,m in enumerate(modes,1)}
def cases():
    allc=old.survivors();dead=old.certified(allc)
    live={k:(i,c) for i,(k,c) in enumerate(allc.items(),2532882) if k not in dead}
    assert len(live)==230 and sum(len(orbit(c)) for _,c in live.values())==1776
    return live

def build(live):
    src=old.dest/'all.cnf'
    with src.open('rb') as inp:assert hashlib.file_digest(inp,'sha256').hexdigest()=='2b4af385c3c77fc1d909a70d29767984211b71c7289ad88baad062da26b8473b'
    own=old.owner_maps();nv=basevars+3
    ex={m:[] for m in modes[:2]};cs=[list(modevar.values())]+[[-a,-b] for a,b in combinations(modevar.values(),2)]
    cs.append([i for i,c in live.values()])
    for i in range(n):
        for j in range(n):
            for d,(a,b) in enumerate(old.DIR[:2]):
                if i+a>=n or j+b>=n:continue
                ids=[v.get((i,j,d)) for v in own]
                for mode,patterns in [('TB',(3,12)),('LR',(6,9))]:
                    for mask in patterns:
                        if any(v is None and mask>>g&1 for g,v in enumerate(ids)):continue
                        terms=[v if mask>>g&1 else -v for g,v in enumerate(ids) if v is not None]
                        nv+=1;ex[mode].append(nv)
                        cs.extend([[-nv,l] for l in terms]);cs.append([nv,*[-l for l in terms]])
                        cs.append([-nv,modevar[mode]])
    for m,ls in ex.items():cs.append([-modevar[m],*ls])
    # NONE has a degree-four junction in the minimal subtree spanning
    # the corners. Its four outgoing directions occur in cyclic order;
    # interior vertices only (a terminal of grid degree 2 can't be this junction).
    junction=[]
    for i in range(1,n-1):
        for j in range(1,n-1):
            for t in range(4):
                nv+=1;junction.append(nv)
                cs.extend([[-nv,own[g][i,j,(g+t)%4]] for g in range(4)])
    cs.append([-modevar['NONE'],*junction])
    # Enumerate all pairs of Boolean existence bits; the old planar
    # compatibility switch forbids simultaneous TB and LR witnesses.
    for tb,lr in ((0,0),(1,0),(0,1)):
        choices=[(u,v,w) for u in (0,1) for v in (0,1) for w in (0,1)
                 if u+v+w==1 and u==tb and v==lr]
        assert choices==[(tb,lr,1-tb-lr)]
    with src.open('rb') as inp,(dest/'base.cnf').open('wb') as out:
        _,_,v,c=inp.readline().split();assert int(v)==basevars
        out.write(f'p cnf {nv} {int(c)+len(cs)}\n'.encode());shutil.copyfileobj(inp,out)
        for cl in cs:out.write((' '.join(map(str,cl))+' 0\n').encode())
    print('edge-pattern IDs',list(map(len,ex.values())),'junction choices',len(junction),'partition',len(live)*3,flush=True)

def search(live,limit):
    from pysat.solvers import Solver
    path=dest/'results.json';res=json.loads(path.read_text()) if '--resume' in sys.argv else {}
    with Solver(name='cadical195') as s,(dest/'base.cnf').open('rb') as f:
        f.readline()
        for l in f:s.add_clause(list(map(int,l.split()[:-1])))
        for k,(i,c) in live.items():
            for m in modes:
                label=k+':'+m
                if res.get(label) in ('SAT','UNSAT'):continue
                s.conf_budget(limit);v=s.solve_limited(assumptions=[i,*c,modevar[m]])
                res[label]={True:'SAT',False:'UNSAT',None:'UNKNOWN'}[v]
                if v:
                    model=set(s.get_model());rows=[''.join('#' if 1+a*n+b in model else '.' for b in range(n)) for a in range(n)]
                    sc=verify(rows);assert sc[0]==sc[-1]==4078
                    (dest/'4078.forest').write_text('\n'.join(rows)+'\n');print('verified',sc)
                print(label,res[label],flush=True);path.write_text(json.dumps(res,indent=2))

def prove(live,groups,tag,sec):
    prefix=dest/tag;fn=prefix.with_suffix('.cnf');pr=prefix.with_suffix('.drat')
    extra=[];active=[]
    for m,keys in groups.items():
        if not keys:continue
        assert len(keys)==len(set(keys)) and set(keys)<=live.keys()
        active.append(modevar[m]);extra.append([-modevar[m],*[live[k][0] for k in keys]])
    assert active;extra.append(active)
    with (dest/'base.cnf').open('rb') as inp,fn.open('wb') as out:
        _,_,v,c=inp.readline().split();out.write(f'p cnf {int(v)} {int(c)+len(extra)}\n'.encode());shutil.copyfileobj(inp,out)
        for cl in extra:out.write((' '.join(map(str,cl))+' 0\n').encode())
    r=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(fn),str(pr)],capture_output=True)
    if r.returncode==0:return False
    assert r.returncode==20
    r=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True)
    assert r.returncode==0 and b's VERIFIED' in r.stdout;prefix.with_suffix('.check').write_bytes(r.stdout)
    prefix.with_suffix('.json').write_text(json.dumps(groups))
    print(tag,'s VERIFIED',sum(map(len,groups.values())),'cases',flush=True);return True

if __name__=='__main__':
    dest.mkdir(exist_ok=True);live=cases()
    if sys.argv[1]=='build':build(live)
    if sys.argv[1]=='search':search(live,int(sys.argv[2]))
    if sys.argv[1]=='prove':
        res=json.loads((dest/'results.json').read_text());assert len(res)==3*len(live)
        gs={m:[k for k in live if res[k+':'+m]=='UNSAT'] for m in modes}
        assert prove(live,gs,'combined',int(sys.argv[2]))
