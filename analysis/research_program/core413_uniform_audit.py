"""Recheck the all-enlargements ledger, including its positive projection model."""
from pathlib import Path
import gzip,hashlib,json,subprocess,sys
from .core413_seams import D,SRC
from .two_gap_transfer_ledger import code,boundary,arrows

PROOFS={
    'raw_core':('147844e50f0c73f13a5e69205b6407c03293d57d056d43a6a16a0587f77ff53d',SRC),
    'pump_1N_all':('78e5b9c0dd37285b76b936a037ba1f59ea5d17b2ae30815279397725ea60781a',None),
    'free_core_0_flush_H7_anchored':('6c403ec37a3508deeb8f5ef06393a54328dc05aa1cde24cc184a766bc8634dc9',None),
    'free_halo_1_primal_0_flush_H7_anchored':('9806e8db283a3b5b655801c557f49f80ada9f09ba9cbe3fab704f4d35dcb137f',None),
    '../exit_box_left_155_270_99_paths_axis1_107to200to3_n413':
        ('8768834ee23f064abceae9c096752c124d74f56cf37e4720b60db6c68ebfd89a',None),
    '../exit_box_left_251_373_114_paths_axis1_203to305to3_n413':
        ('08acb26b563487cde76a3e164b68c44f3ce86f888a7f2d6f147de98729d13b85',None)}

def digest(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

def replay():
    for name,(h,src) in PROOFS.items():
        p=D/name;cnf=src or p.with_suffix('.cnf')
        assert digest(cnf)==h
        data=p.with_suffix('.check').read_bytes()
        if '--drat' in sys.argv:
            data=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(p.with_suffix('.drat'))],
                                capture_output=True,check=True).stdout
        assert b's VERIFIED' in data
        print(name,*[x for x in data.decode().splitlines() if 'resolution steps' in x])
    # Verify inclusion, not just that the vertical abstraction is UNSAT.
    def read(p):
        with p.open('rb') as fd:
            fd.readline();return {tuple(sorted(map(int,l.split()[:-1]))) for l in fd}
    core=read(SRC)
    with SRC.open('rb') as fd:
        assert int(fd.readline().split()[3])==sum(1 for _ in fd)==179213
    assert core<=read(D/'pump_1N_all.cnf')
    print('all 179213 source clauses accounted for;',len(core),'distinct after sorting')
    for name,a,b in [('free_core_0_flush_H7_anchored',110,173),('free_halo_1_primal_0_flush_H7_anchored',110,227)]:
        p=D/name;rec=json.loads(p.with_suffix('.json').read_text())
        ds={int(k) for k,v in rec.items() if v=='VERIFIED'};assert ds==set(range(a,b+1,3))
        tags=json.load(gzip.open(D/'names.gz','rt'))
        # A positive disjunction of exactly these physical star IDs
        # selects the union checked by the DRAT replay.
        with p.with_suffix('.cnf').open('rb') as fd:
            fd.seek(-1024,2);last=fd.read().splitlines()[-1]
        assert {tuple(tags[str(z)]) for z in map(int,last.split()[:-1])}=={('s',0,d) for d in ds}
    bits=(D/'stable_halo_1_primal_182_flush_stationary_H8.bits').read_bytes()
    assert hashlib.sha256(bits).hexdigest()=='e59ef0f596eeb97a9e84adc99b5ba7fdda4652d5fda0b2326081851a77b892cb'
    def value(z):return bool(bits[(z-1)//8]&(1<<((z-1)%8)))
    ts=json.load(gzip.open(D/'names.gz','rt'))
    assert [t[2] for z,t in ts.items() if t[0]=='s' and value(int(z))]==[182]
    for name,h in [('flush_halo_1_primal','49959b0233f6561fc4f0141b3bd52b188257d8d1422fdc57da539adc0fe3ef97'),
                   ('ports_halo_1_primal_1_flush_stationary_H8','d5c522e1bb31e12ebc09f8c03f08ad932f8603efbe349b4183ebab815943d090')]:
        p=D/(name+'.cnf');assert digest(p)==h
        with p.open('rb') as fd:
            total=int(fd.readline().split()[3]);i=0
            for l in fd:
                assert any(value(abs(v))==(v>0) for v in map(int,l.split()[:-1]));i+=1
            assert i==total;print('stationary projection checked',i,'clauses',name)

def sizes():
    for n in (413,455,497,539,581,623,665):
        for lo,hi,w,h in ((107,200,270,99),(203,305,373,114)):
            assert all(code(j,n)==code(j,413) for j in range(-2,w+2))
            assert all(code(i,n)==code(i,413) for i in range(-2,h+2))
            # The marked frame, the rooted perimeter directions and the
            # exit-relative tooth exceptions are unchanged in the NW window.
            ps=set((0,j) for j in range(w))|{(i,0) for i in range(h)}
            for d in range(lo,hi+1,3):
                p,q=arrows(n,d),arrows(413,d)
                assert all(p[z]==q[z] and boundary(n)[z]==boundary(413)[z] for z in ps)
        survivors=[d for d in range(107,n-107,3) if min(d,n-1-d)>305]
        assert survivors==[308+3*j for j in range(max(0,14*((n-413)//42)-67))]
        print(n,'remaining two-gap exits',len(survivors),survivors[:3])
if __name__=='__main__':replay();sizes()
