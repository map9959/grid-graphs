"""All-length physical overlap relaxation of the smaller 413 proof.

Insert 42u and 42v columns, 42(u+v) rows.  On each cut track use an
endpoint relation, never equality of an inserted slice with an old slice.
"""
from itertools import product,combinations
from functools import lru_cache
from array import array
from pathlib import Path
from collections import Counter
import gzip,json,subprocess,sys
from pysat.solvers import Solver
from .core413_seams import D
from .saturated_tile_phase import ROW
from .tile_family_lp import projected,typ
from .odd_frames import frame,DIR
from .two_gap_board import Stream

N=413
CUTS=(193,19,394)
def otag():return next((s[8:] for s in sys.argv if s.startswith('--owner=')),'')
def anchored():return '--anchored' in sys.argv
def prep(base):
    if base=='core':src=Path('target/core371_lift/halo_1_primal.core')
    else:src=Path('target/core371_lift')/(base+'.cnf') if base!='full' else Path('target/two_gap_413_0011_axis_ordinary_linked.cnf')
    assert src.exists()
    if '--flush' in sys.argv:
        p=D/('flush_'+base+('_anchored' if anchored() else '')+'.cnf')
        if anchored():assert '--positive' not in sys.argv
        y,l,r=CUTS
        subprocess.run(['target/core_seam_filter',str(D/'loc.bin'),*map(str,(y,0 if anchored() else l,r)),str(src),str(p)],check=True)
        return p
    loc=array('I');loc.frombytes((D/'loc.bin').read_bytes())
    allowed=bytearray(len(loc))
    y,l,r=CUTS
    for z,t in enumerate(loc):
        i,j=(t>>16)-1,(t&65535)-1
        if min(abs(i-y),abs(j-l),abs(j-r))<=2:allowed[z]=1
    fn=D/'keep.bin';fn.write_bytes(allowed)
    p=D/f'pieces_{base}.cnf'
    subprocess.run(['target/core_halo',str(fn),'0',str(src),str(p)],check=True)
    return p

@lru_cache(None)
def closure(words,axis,activity,positive,steps,stationary):
    # Coordinate order is inward from the side and then along its tangent.
    # -1: outside deep axis rule; 2: no row activation imposed.
    def usable(node):
        for m,active in zip(node,activity):
            if active<0:continue
            if m&16 and m&(40 if axis==1 else 130):return False
            if active==1 and m not in ROW:return False
            if active==0 and m&16 and m&130:return False
        return True
    adj={}
    for a,b,c,d in words:
        x,y=(a,c),(b,d)
        if usable(x) and usable(y):adj.setdefault(x,set()).add(y);adj.setdefault(y,set())
    # One graph step is a physical tile column. The endpoints are three
    # steps apart at 413; each insertion adds fourteen. Union until an
    # entire ordered-pair relation recurs, not just a cardinality.
    rel={x:{x} for x in adj};out={x:set() for x in adj};saved=set()
    for k in range(200):
        if k%14==steps and (not positive or k>=steps+14):
            sig=frozenset((a,b) for a,S in rel.items() for b in S)
            if sig in saved:break
            saved.add(sig)
            for x,Y in rel.items():
                if stationary and len(saved)>1:out[x].intersection_update(Y)
                else:out[x]|=Y
        rel={a:set().union(*(adj[x] for x in S)) for a,S in rel.items()}
    else:raise AssertionError('relation did not stabilize')
    return out

def make(base,positive):
    n=N;k=(n-2)//3;K=k-1
    marks=array('I');marks.frombytes((D/'marks.bin').read_bytes())
    M=lambda i,j:marks[n*i+j]
    ts={int(z):t for z,t in json.load(gzip.open(D/'names.gz','rt')).items()}
    flags={t[2]:v for v,t in ts.items() if t[0]=='s'}
    assert sorted(flags)==list(range(107,306,3))
    inds=list(range(14,n-14,3));axis=next(z for z,t in ts.items() if t[0]=='axis')
    row={i:axis+1+h for h,i in enumerate(inds)}
    flush='--flush' in sys.argv;stationary='--stationary' in sys.argv
    tag=('_flush' if flush else '')+('_stationary' if stationary else '')+('_H'+otag() if otag() else '')+('_anchored' if anchored() else '')
    f=Stream(D/f'ports_{base}_{int(positive)}{tag}.cnf')
    nv=2716317
    def fresh():
        nonlocal nv
        nv+=1;return nv
    if otag():
        assert flush
        from .core413_owner_tracks import install
        install(n,CUTS,positive,stationary,int(otag()),marks,fresh,f.append)
    if stationary:
        # The trimmed core may not retain every counter clause. A positive
        # projection witness must still choose just one short-side exit.
        f.append(list(flags.values()))
        for z,w in combinations(flags.values(),2):f.append([-z,-w])
    ycut,left,right=CUTS;B=projected(3,5)
    rim={tuple(map(int,s.split(','))):v for s,v in json.load(gzip.open(D/'rim.gz','rt')).items()}
    # These directions follow from the actual perimeter paths and the
    # specified ordinary exit. Each such clause uses only retained sites.
    allow=lambda i,j:min(abs(i-ycut),abs(j-left),abs(j-right))>2
    words=frame(n,(0,0,1,1))
    for exit,z in flags.items():
        q=[(0,0),(0,exit)];parent={q[0]:-1,q[1]:1}
        for i,j in q:
            for s,(a,b) in enumerate(DIR):
                v=i+a,j+b
                if v in words and min(*v,n-1-v[0],n-1-v[1])==0 and v not in parent and (words[i,j] or words[v]):
                    q.append(v);parent[v]=(s+2)%4
        for (i,j),s in parent.items():
            if s>=0 and allow(i,j):f.append([-z,rim[i,j][s]])
    for (i,j),dirs in rim.items():
        if min(i,j,n-1-i,n-1-j)!=2 or not allow(i,j):continue
        for s,(a,b) in enumerate(DIR):
            v=i+2*a,j+2*b
            if v in words and min(*v,n-1-v[0],n-1-v[1])==0 and words[v]:
                f.append(([flags[j]] if i==2 and j in flags else [])+[-M(i,j),dirs[s]])
    for vert,cut in ((False,left),(False,right),(True,ycut)):
        cuts=[left,right] if vert else [ycut]
        for r in range(K):
            norm=1+3*r
            if any(norm-2<=c<=norm+7 for c in cuts):continue
            far=r>K-1-r
            # Normal reflection puts the nearest physical side at the top.
            # Tangential coordinates increase in the direction of its arrows.
            rev=not far if vert else far or cut==right
            # west arrow north, east arrow south; south arrow west; on
            # the northern arm both pieces point toward the middle exit.
            wordsB=tuple(B[typ(min(r,K-1-r),K),6])
            centers=[norm+(4-3*h if far else 1+3*h) for h in (0,1)]
            deep=[i in row for i in centers]
            act=[(0,1) if ok and not vert else (2,) if ok else (-1,) for ok in deep]
            opts={}
            for aa in product(*act):
                opts[aa]=closure(wordsB,2 if vert else 1,aa,positive or vert,1 if flush else 3,stationary)
            nodes=sorted({x for rel in opts.values() for x in rel})
            eps=[]
            ends=(cut-3,cut) if flush else (cut-6,cut+3)
            for start in (ends[::-1] if rev else ends):
                state={};tiles={}
                for x in nodes:
                    z=fresh();state[x]=z
                    for h,m in enumerate(x):
                        if (h,m) not in tiles:
                            tag=fresh();tiles[h,m]=tag
                            for i,j in product(range(3),repeat=2):
                                a=norm+(5-(3*h+i) if far else 3*h+i);b=start+(2-j if rev else j)
                                v=M(b,a) if vert else M(a,b)
                                f.append([-tag,v if m>>(3*i+j)&1 else -v])
                        f.append([-z,tiles[h,m]])
                f.append(list(state.values()));eps.append(state)
            for aa,rel in opts.items():
                guard=[(-1 if a else 1)*row[i] for a,i in zip(aa,centers) if a in (0,1)]
                for x,z in eps[0].items():f.append([*guard,-z,*[eps[1][b] for b in sorted(rel.get(x,()))]])
    f.to_file(str(f.path));return f.path,flags

def run(base,budget,positive):
    p=prep(base);ports,flags=make(base,positive)
    tag=('_flush' if '--flush' in sys.argv else '')+('_stationary' if '--stationary' in sys.argv else '')+('_H'+otag() if otag() else '')+('_anchored' if anchored() else '')
    ans={}
    only=next((int(s[7:]) for s in sys.argv if s.startswith('--only=')),None)
    rtag=tag+(f'_d{only}' if only is not None else '')
    with Solver(name='cadical195') as s:
        for file in (p,ports):
            with file.open('rb') as fd:
                fd.readline()
                for l in fd:s.add_clause(list(map(int,l.split()[:-1])))
        for d,z in sorted(flags.items()):
            if only is not None and d!=only:continue
            s.conf_budget(budget);v=s.solve_limited(assumptions=[z]);ans[d]=str(v)
            if v and '--stationary' in sys.argv:
                model=s.get_model();pack=bytearray((len(model)+7)//8)
                for lit in model:
                    if lit>0:pack[(lit-1)//8]|=1<<((lit-1)%8)
                (D/f'stable_{base}_{d}{tag}.bits').write_bytes(pack)
                break
        print('decisions',Counter(ans.values()),'pending', [d for d,v in ans.items() if v=='False'],flush=True)
    dead=[flags[d] for d,v in ans.items() if v=='False']
    if dead and '--stationary' not in sys.argv:
        import shutil
        cert=D/f'free_{base}_{int(positive)}{rtag}.cnf';pr=cert.with_suffix('.drat')
        with p.open('rb') as a,ports.open('rb') as b,cert.open('wb') as out:
            _,_,v,c=a.readline().split();_,_,w,e=b.readline().split()
            out.write(f'p cnf {max(int(v),int(w))} {int(c)+int(e)+1}\n'.encode());shutil.copyfileobj(a,out);shutil.copyfileobj(b,out)
            out.write((' '.join(map(str,dead))+' 0\n').encode())
        with cert.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t','240',str(cert),str(pr)],stdout=fd).returncode
        if rc==20:
            chk=subprocess.run(['target/drat-trim/drat-trim',str(cert),str(pr)],check=True,capture_output=True).stdout
            assert b's VERIFIED' in chk;cert.with_suffix('.check').write_bytes(chk)
            ans={d:('VERIFIED' if v=='False' else v) for d,v in ans.items()};print('s VERIFIED exits',len(dead))
        else:assert rc==0;print('UNKNOWN union')
    (D/f'free_{base}_{int(positive)}{rtag}.json').write_text(json.dumps(ans)+'\n')
if __name__=='__main__':run(sys.argv[1],int(sys.argv[2]),'--positive' in sys.argv)
