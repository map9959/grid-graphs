"""Localize the unique defect after grounding a one-gap perimeter."""
from pathlib import Path
import subprocess
from pysat.solvers import Solver
from .defect_window import table,window
from .odd_frames import frame,DIR

def run(R,open_only=False):
    n=119;M=n//2;B=R+7;t=table(n)
    for region in ('interior','edge','root'):
        if open_only and region!='root':continue
        # All four NW corner words occur up to reflection/rotation. Reroot
        # at NW: changing corner roots reverses only perimeter edges.
        words=[(0,1,1,1),(2,1,1,1),(1,0,1,1),(3,0,1,1)] if region=='root' else [(0,1,1,1)]
        for w in words:
            if open_only and w[0]!=0:continue
            m=frame(n,w);parent={(0,0):-1};todo=[(0,0)]
            for i,j in todo:
                for d,(a,b) in enumerate(DIR):
                    u=i+a,j+b
                    if u in m and min(*u,n-1-u[0],n-1-u[1])==0 and u not in parent and (m[i,j] or m[u]):
                        parent[u]=(d+2)%4;todo.append(u)
            assert len(parent)==4*n-4
            # For an edge far from corners choose the root at the end
            # toward which its tangential path points (or reflect).
            def emit(f,bit,flags):
                if region=='edge':ib=range(B+R+3);jb=range(M-R,M+R+5)
                elif region=='root':ib=jb=range(B+R+3)
                else:ib=jb=range(M-R,M+R+5)
                for u,z in m.items():
                    if u[0] in ib and u[1] in jb:f.append([bit(*u) if z else -bit(*u)])
                keep=[]
                with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
                    while s.solve():
                        v=set(s.get_model());k,=[k for k,x in flags.items() if x in v]
                        keep.append(k);s.add_clause([-flags[k]])
                for k in keep:f.append([-flags[k]])
                stem=Path(f'target/one_gap_sites_r{R}_{region}_{w[0]}');cnf=stem.with_suffix('.cnf');proof=stem.with_suffix('.drat')
                f.to_file(str(cnf));assert subprocess.run(['target/cadical/build/cadical',str(cnf),str(proof)],capture_output=True).returncode==20
                res=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(proof)],capture_output=True)
                assert res.returncode==0 and b's VERIFIED' in res.stdout
                print(region,w[0],'s VERIFIED','stars',sorted((i,j) for s,i,j in keep if s=='s'),'patches',sorted((i,j) for s,i,j in keep if s=='p'),flush=True)
            window(n,region,R,t,matching=True,orient=parent,emit=emit)
if __name__=='__main__':
    import sys
    run(int(sys.argv[1]),'--open' in sys.argv)
