"""Verify the enlarged core clause inclusion and the two projection models."""
from pathlib import Path
from hashlib import file_digest
from .two_gap_core_lift import OUT

def audit():
    root=Path('target')
    fp=root/'two_gap_413_0011_axis_ordinary_linked.cnf'
    with fp.open('rb') as f:assert file_digest(f,'sha256').hexdigest()=='75fc28810ae7ea53acb69653d35f00659b8c1fbed9f4c4ffa03ec448531aa4da'
    for stem,count,h in [('halo_1',3990200,'7a6193ca8354d8b3fd11f40fea27351d74bff0e34596714b3c5409d141bc46f6'),
                         ('halo_1_primal',1912722,'4a7abca35d2c7b481c432b4f535264ddb95c51aeb4388862faa8091d3d86743b')]:
        subset=OUT/(stem+'.cnf')
        with subset.open('rb') as f:assert file_digest(f,'sha256').hexdigest()==h
        with fp.open('rb') as source,subset.open('rb') as sub:
            assert source.readline().split()[2:]==[b'2716317',b'32245288']
            assert sub.readline().split()[2:]==[b'2716317',str(count).encode()]
            line=sub.readline();n=0
            for original in source:
                if original==line:
                    n+=1;line=sub.readline()
                    if not line:break
            assert not line and n==count
        print('checked ordered subformula:',n,'unchanged clauses on side-413 variables')

def partial_model(stem):
    from pysat.solvers import Solver
    p=OUT/(stem+'.cnf')
    # Complete any literals omitted from the partial CaDiCaL log.
    with p.open('rb') as fd:
        nv=int(fd.readline().split()[2]);bits=bytearray(nv+1)
    with p.with_suffix('.log').open() as fd:
        for line in fd:
            if not line.startswith('v '):continue
            for x in map(int,line.split()[1:]):
                if x:
                    s=1 if x>0 else 2;assert bits[abs(x)] in (0,s);bits[abs(x)]=s
    def clauses():
        with p.open('rb') as fd:
            fd.readline()
            for l in fd:yield list(map(int,l.split()[:-1]))
    def sat(c):return any(bits[abs(x)]==(1 if x>0 else 2) for x in c)
    with Solver(name='cadical195') as sol:
        for c in clauses():
            if not sat(c):sol.add_clause([x for x in c if not bits[abs(x)]])
        assert sol.solve()
        for x in sol.get_model():
            if not bits[abs(x)]:bits[abs(x)]=1 if x>0 else 2
    n=0
    for c in clauses():assert sat(c);n+=1
    print(stem,'partial-model replay:',n,'clauses satisfied')
if __name__=='__main__':
    audit()
    for stem in ('shared_413','halo_0','halo_1_face'):partial_model(stem)
