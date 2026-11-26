"""Opposite the normalized star, two complete clean sides meet at SE."""
from itertools import product
from pathlib import Path
from hashlib import file_digest
import subprocess,sys
from .defect_window import table,window,DIR
from .saturated_tile_phase import axis_clauses
from .slit_star_transfer import frame_path

def test(n,width,rootnum,sec,side=0,axis=0,word=-1):
    dom={(i,j) for i,j in product(range(n),repeat=2) if (max(i,j) if not side else (i if side==1 else j))>=n-width}
    root=((n-1,n-1),(0,0),(n-1,0),(0,n-1))[rootnum]
    def emit(f,bit,flags,arc,sheet):
        records=[]
        for w in range(16):
            marks,_=frame_path(n,w);path={root:-1};todo=[root]
            for i,j in todo:
                for d,(a,b) in enumerate(DIR):
                    v=i+a,j+b
                    if v in path or v not in marks or min(*v,n-1-v[0],n-1-v[1])!=0:continue
                    if marks[i,j] or marks[v]:path[v]=(d+2)%4;todo.append(v)
            assert len(path)==4*n-4
            record=[(bit(*u),m) for u,m in marks.items() if u in dom]
            record.extend((arc(*u,d),int(d==p)) for u,p in path.items() if u in dom for d,(a,b) in enumerate(DIR)
                          if (u[0]+a,u[1]+b) in dom)
            records.append(dict(record))
        for i,j in dom:
            near=[(i+a,j+b) for a,b in DIR if 0<=i+a<n and 0<=j+b<n]
            if all(v in dom for v in near):f.append([bit(i,j),*(bit(*v) for v in near)])
        top=max(f.nv,max(records[0]));sel=[top+1+i for i in range(16)];f.append(sel)
        for z in sorted(records[0]):
            vals=[z*(1 if r[z] else -1) for r in records]
            if len(set(vals))==1:f.append([vals[0]])
            else:f.extend([[-s,v] for s,v in zip(sel,vals)])
        if word>=0:f.append([sel[word]])
        ax=f.nv+1;axis_clauses(f,bit,n,dom)
        if axis:f.append([ax if axis==1 else -ax])
        stem=Path(f'target/clean_side_axis_{n}_{width}_{rootnum}'+(f'_{side}_{axis}_{word}' if side or axis or word>=0 else ''));cnf=stem.with_suffix('.cnf');proof=stem.with_suffix('.drat')
        f.to_file(str(cnf));f.clauses.clear()
        with cnf.open('rb') as fd:print('side',n,'width',width,'root',root,'excluded star columns <',n-width,'sha256',file_digest(fd,'sha256').hexdigest(),flush=True)
        with stem.with_suffix('.log').open('w') as log:
            s=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(cnf),str(proof)],stdout=log).returncode
        if s==20:
            out=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(proof)],capture_output=True,check=True).stdout
            assert b's VERIFIED' in out;stem.with_suffix('.check').write_bytes(out);print('UNSAT s VERIFIED')
        else:print('regional SAT' if s==10 else 'UNKNOWN')
    window(n,'rim',1,table(n),domain=dom,root_site=root,want=False,matching=True,emit_graph=emit)
if __name__=='__main__':test(*map(int,sys.argv[1:]))
