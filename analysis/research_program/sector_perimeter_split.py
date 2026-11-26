"""D4 cover of the physical 4078 corner/perimeter assignments."""
from itertools import product
from .sector_corner_split import src,coverage,certified_summary,verify,Path,json,subprocess,shutil,sys
from .square_dual_physical import trans

n=109
corners=[trans(0,0,n,g) for g in range(4)]
ports=[trans(i,j,n,g) for g in range(4) for i,j in [(0,1),(1,0)]]
sites=corners+ports
def rotate(w,g):
    a={trans(*p,n,g):b for p,b in zip(sites,w)}
    return ''.join(a[p] for p in sites)
def cube(w):return [(1+i*n+j)*(1 if b=='1' else -1) for (i,j),b in zip(sites,w)]
def continuation(w,mask,distance=2):
    out=[]
    for g,corner in enumerate(corners):
        d=w[4+2*g:6+2*g].index('1')
        i,j=(b+distance*(a-b) for a,b in zip(ports[2*g+d],corner))
        out.append((1+i*n+j)*(1 if mask>>g&1 else -1))
    return out
def groups():
    rem=certified_summary();groups={}
    for bits in product('01',repeat=12):
        w=''.join(bits);orb={rotate(w,g) for g in range(8)}
        legal=all(rem[z[:6]]=='UNKNOWN' for z in orb)
        assert legal==(w[:4].count('1')>=3 and all(w[j]!=w[j+1] for j in range(4,12,2)))
        if legal:groups[min(orb)]=sorted(orb)
    assert sum(map(len,groups.values()))==80
    print('4096 assignments checked, 80 physical signatures,',len(groups),'disjoint D4 orbits',flush=True)
    return groups
dest=Path('target/sector_perimeter')
def search(gs,limit,which):
    from pysat.solvers import Solver
    with Solver(name='cadical195') as s,src.open('rb') as inp:
        inp.readline()
        for line in inp:s.add_clause(list(map(int,line.split()[:-1])))
        for rep,orb in sorted(gs.items()):
            if (dest/(rep+'.check')).exists():continue
            w=orb[which%len(orb)]
            s.conf_budget(limit);v=s.solve_limited(assumptions=cube(w))
            print(rep,'via',w,{True:'SAT',False:'UNSAT',None:'UNKNOWN'}[v],flush=True)
            if v is None:continue
            if v:
                m=set(s.get_model())
                rows=[''.join('#' if 1+i*n+j in m else '.' for j in range(n)) for i in range(n)]
                score=verify(rows);assert score[0]==score[-1]==4078
                (dest/(rep+'.forest')).write_text('\n'.join(rows)+'\n');print(score);return
            (dest/(rep+'.cube')).write_text(w+'\n')
def prove(gs,seconds):
    for rep,orb in sorted(gs.items()):
        out=dest/(rep+'.check');case=dest/(rep+'.cube')
        if not case.exists() or out.exists():continue
        w=case.read_text().strip();assert w in orb
        cnf=dest/'case.cnf';pr=dest/'case.drat'
        with cnf.open('wb') as f,src.open('rb') as s:
            assert s.readline().split()==[b'p',b'cnf',b'644884',b'4370519']
            f.write(b'p cnf 644884 4370531\n');shutil.copyfileobj(s,f)
            for z in cube(w):f.write(f'{z} 0\n'.encode())
        r=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(cnf),str(pr)],capture_output=True)
        if r.returncode==0:print(rep,'proof search UNKNOWN',flush=True);continue
        assert r.returncode==20
        r=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(pr)],capture_output=True)
        assert r.returncode==0 and b's VERIFIED' in r.stdout
        out.write_bytes(w.encode()+b'\n'+r.stdout)
        print(rep,'via',w,'s VERIFIED; signatures',len(orb),flush=True)

def refine(gs,limit):
    from pysat.solvers import Solver
    good=[];undecided=0
    with Solver(name='cadical195') as s,src.open('rb') as inp:
        inp.readline()
        for line in inp:s.add_clause(list(map(int,line.split()[:-1])))
        for rep in sorted(gs):
            bad=[]
            for m in range(16):
                lits=cube(rep)+continuation(rep,m)
                s.conf_budget(limit)
                r=s.solve_limited(assumptions=lits)
                if r is False:bad.append(m);good.append(lits)
                elif r is None:undecided+=1
                else:
                    x=set(s.get_model());rows=[''.join('#' if 1+i*n+j in x else '.' for j in range(n)) for i in range(n)]
                    score=verify(rows);assert score[0]==score[-1]==4078
                    (dest/(rep+'.forest')).write_text('\n'.join(rows)+'\n');print(score);return
            print(rep,'second-site masks UNSAT',bad,flush=True)
    (dest/'refined.json').write_text(json.dumps(good))
    print('refined decisions',len(good),'undecided',undecided,flush=True)

def combined(seconds,tag='refined'):
    group=json.loads((dest/(tag+'.json')).read_text());assert group
    gs=groups()
    possible={tuple(cube(w)+continuation(w,m)) for w in gs for m in range(16)}
    if tag=='extra':possible={tuple(rotated_units(c,2)) for c in possible}
    assert len(group)==len(set(map(tuple,group))) and set(map(tuple,group))<=possible
    cnf=dest/(tag+'.cnf');pr=dest/(tag+'.drat')
    with cnf.open('wb') as out,src.open('rb') as inp:
        _,_,nv,nc=inp.readline().split();nv=int(nv)
        extra=[list(range(nv+1,nv+1+len(group)))]
        for i,c in enumerate(group,nv+1):extra.extend([[-i,x] for x in c])
        out.write(f'p cnf {nv+len(group)} {int(nc)+len(extra)}\n'.encode());shutil.copyfileobj(inp,out)
        for c in extra:out.write((' '.join(map(str,c))+' 0\n').encode())
    r=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(cnf),str(pr)],capture_output=True)
    if r.returncode==0:print('combined search UNKNOWN');return
    assert r.returncode==20
    r=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(pr)],capture_output=True)
    assert r.returncode==0 and b's VERIFIED' in r.stdout
    (dest/(tag+'.check')).write_bytes(r.stdout);print(tag,'cases',len(group),'s VERIFIED')

def certified(gs):
    group=[]
    for w in sorted(gs):
        if w.startswith('1111'):remain={7,11,13,14,15}
        elif w=='011101010101':remain={7,11,13,15}
        else:remain={15}
        group.extend(cube(w)+continuation(w,m) for m in range(16) if m not in remain)
    assert len(group)==161
    return group

def rotated_units(units,g):
    ans=[]
    for z in units:
        i,j=trans(*divmod(abs(z)-1,n),n,g)
        ans.append((1+i*n+j)*(1 if z>0 else -1))
    return ans

def finish(gs,limit):
    from pysat.solvers import Solver
    known={tuple(c) for c in certified(gs)};extra=[]
    with Solver(name='cadical195') as s,src.open('rb') as inp:
        inp.readline()
        for l in inp:s.add_clause(list(map(int,l.split()[:-1])))
        for rep in gs:
            for m in range(16):
                c=cube(rep)+continuation(rep,m)
                if tuple(c) in known:continue
                # Move corner 2 (SE) to the root instead of fixing NW.
                units=rotated_units(c,2)
                s.conf_budget(limit);res=s.solve_limited(assumptions=units)
                print(rep,m,'via SE root',res,flush=True)
                if res is None:continue
                if res is False:extra.append(units)
                else:
                    x=set(s.get_model());rows=[''.join('#' if 1+i*n+j in x else '.' for j in range(n)) for i in range(n)]
                    score=verify(rows);assert score[0]==score[-1]==4078
                    (dest/(rep+'.forest')).write_text('\n'.join(rows)+'\n');print(score);return
    (dest/'extra.json').write_text(json.dumps(extra))

def tally(gs):
    def key(c):return min(tuple(sorted(rotated_units(c,g))) for g in range(8))
    banned={key(c) for c in certified(gs)}
    w='011101010101';banned.add(key(cube(w)+continuation(w,13)))
    allkeys={};total=live=0
    for rep,orb in gs.items():
        for w in orb:
            for m in range(16):
                k=key(cube(w)+continuation(w,m));allkeys[k]=k not in banned
                total+=1;live+=int(allkeys[k])
    assert total==80*16 and banned<=allkeys.keys()
    print('physical second-site assignments',total,'remaining',live,
          'D4 classes',len(allkeys),'remaining',sum(allkeys.values()))
if __name__=='__main__':
    coverage();gs=groups();dest.mkdir(exist_ok=True)
    if sys.argv[1]=='search':search(gs,*map(int,sys.argv[2:]))
    elif sys.argv[1]=='prove':prove(gs,int(sys.argv[2]))
    elif sys.argv[1]=='refine':refine(gs,int(sys.argv[2]))
    elif sys.argv[1]=='finish':finish(gs,int(sys.argv[2]))
    elif sys.argv[1]=='combined':combined(int(sys.argv[2]))
    elif sys.argv[1]=='certified':
        (dest/'refined.json').write_text(json.dumps(certified(gs)))
        combined(int(sys.argv[2]))
    elif sys.argv[1]=='extra-proof':
        w='011101010101'
        (dest/'extra.json').write_text(json.dumps([rotated_units(cube(w)+continuation(w,13),2)]))
        combined(int(sys.argv[2]),'extra')
    elif sys.argv[1]=='tally':tally(gs)
    else:
        for r,o in sorted(gs.items()):print(r,len(o))
