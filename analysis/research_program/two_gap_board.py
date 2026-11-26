"""Full-board test of the odd target, conditional on two perimeter gaps."""
from .defect_window import table,window
from .odd_frames import frame,rotate,PAT
from .extend_forest_28 import verify
from itertools import product
from pathlib import Path
import subprocess,sys

class Stream:
    """Same clause order and numbering as PySAT; reserve the header in place."""
    def __init__(self,path):
        self.path=path;self.fd=path.open('wb');self.fd.write(b' '*63+b'\n');self.nv=self.count=0
    def append(self,c):
        self.nv=max(self.nv,max(map(abs,c),default=0));self.count+=1
        self.fd.write((' '.join(map(str,c))+' 0\n').encode())
    def extend(self,cs):
        for c in cs:self.append(c)
    def to_file(self,path):
        assert Path(path)==self.path
        self.fd.seek(0);self.fd.write(f'p cnf {self.nv} {self.count}'.encode().ljust(63)+b'\n');self.fd.close()

def run(n,seconds,chosen,map_ids=None):
    assert n>=119 and (n-35)%42==0
    words=[w for w in product(range(4),repeat=4)
           if sum(x in (0,2) for x in w)==2 and min(rotate(w,g) for g in range(8))==w]
    if chosen!='all':words=[tuple(map(int,chosen))]
    ordinary='--ordinary-bridge' in sys.argv
    if ordinary:assert chosen=='0011'
    linked='--linked-exits' in sys.argv
    if linked:assert ordinary and '--axis' in sys.argv and n>=329
    sites={('s',0,d) for d in range(107,n-107,3)} if linked else None
    path=Path(f'target/two_gap_{n}_{chosen}'+('_axis' if '--axis' in sys.argv else '')+('_ordinary' if ordinary else '')+('_linked' if linked else '')+'.cnf')
    def test(f,bit,flags):
        # Test the disjunction of frames; the only allowed nonzero atom
        # in this formula is a boundary star. One indicator per frame.
        nv=f.nv;selectors=[]
        for j,w in enumerate(words):
            assert len(w)==4 and sum(x in (0,2) for x in w)==2
            sel=nv+j+1;selectors.append(sel);marked=frame(n,w)
            for (i,k),v in marked.items():f.append([-sel,bit(i,k) if v else -bit(i,k)])
            # Prescribe every arrow in the perimeter component of NW.
            # No exit may occur in that component.
            todo=[(0,0)];seen=set(todo)
            for i,k in todo:
                if ('s',i,k) in flags:f.append([-sel,-flags['s',i,k]])
                for a,b in ((0,1),(0,-1),(1,0),(-1,0)):
                    z=i+a,k+b
                    if z in marked and min(*z,n-1-z[0],n-1-z[1])==0 and z not in seen and (marked[i,k] or marked[z]):
                        seen.add(z);todo.append(z)
        f.append(selectors)
        axis='--axis' in sys.argv
        if axis:
            from .saturated_tile_phase import axis_clauses
            axisvar=f.nv+1
            axis_clauses(f,bit,n)
            if linked:
                assert set(flags)==sites
                f.append([axisvar]) # actual vertical bond, hence no horizontal center bond
                print('shared physical marks and edge owners; exit columns',len(flags),
                      min(k[2] for k in flags),max(k[2] for k in flags),flush=True)
        if ordinary:
            # Crop components cannot contain a gap tooth and any other
            # tooth: the sole two-tooth component has ordinary endpoints.
            start=f.nv
            def label(i,j,h):return start+1+2*((n-4)*(i-2)+j-2)+h
            for i,j in product(range(2,n-2),repeat=2):
                m=bit(i,j)
                if min(i,j,n-1-i,n-1-j)==2:
                    code={(2,2):1,(2,n-3):2}.get((i,j),0)
                    for h in (0,1):f.append([-m,label(i,j,h)*(1 if code>>h&1 else -1)])
                for x,y in ((i+1,j),(i,j+1)):
                    if max(x,y)>n-3:continue
                    for h in (0,1):
                        u,v=label(i,j,h),label(x,y,h)
                        for guard in (m,bit(x,y)):f.extend([[-guard,-u,v],[-guard,u,-v]])
            for i,j in ((2,0),(0,n-3)):
                if ('s',i,j) in flags:f.append([-flags['s',i,j]])
        proof=path.with_suffix('.drat');f.to_file(str(path))
        print('side',n,'complete board; frame classes',len(words),'variables',f.nv,'clauses',f.count if isinstance(f,Stream) else len(f.clauses),flush=True)
        if map_ids:
            from inspect import getclosurevars
            map_ids(getclosurevars(bit).nonlocals['vp'],nv,path)
            if not seconds:return
        with path.with_suffix('.log').open('w') as out:
            p=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(path),str(proof)],stdout=out)
        if p.returncode==20:
            q=subprocess.run(['target/drat-trim/drat-trim',str(path),str(proof)],capture_output=True)
            assert q.returncode==0 and b's VERIFIED' in q.stdout
            path.with_suffix('.check').write_bytes(q.stdout)
            print('two-gap exclusion: s VERIFIED',flush=True)
        elif p.returncode==10:
            model={int(v) for line in path.with_suffix('.log').read_text().splitlines() if line.startswith('v ') for v in line[2:].split()}
            rows=[''.join('#' if bit(i,j) in model else '.' for j in range(n)) for i in range(n)]
            v=verify(rows);k=(n-2)//3;assert v[0]==v[-1]==3*k*k+7*k-(k-5)//7
            path.with_suffix('.forest').write_text('\n'.join(rows)+'\n');print('verified forest',v,flush=True)
        else:print('no decision; solver return',p.returncode,flush=True)
        if p.returncode!=20 or not axis:proof.unlink(missing_ok=True)
    sink=Stream(path) if '--stream' in sys.argv else None
    window(n,'rim',n,table(n),matching=True,emit=test,exit_only=True,clause_sink=sink,defects=sites)
if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2]),sys.argv[3])
