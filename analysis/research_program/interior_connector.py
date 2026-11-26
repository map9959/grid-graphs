"""Full-square common connector decision, including arcs beyond the annulus."""
from pathlib import Path
from .rim_connector import install,reverse_charge
from .defect_window import window,table,DIR,product
from .odd_frames import frame
from .extend_forest_28 import verify
import subprocess,sys

CODES=('0011','0013','0031','0033','0112','0132','0211','0213','0231','0312')
def run(n,seconds):
    data=table(n);frames={c:frame(n,tuple(map(int,c))) for c in CODES}
    def emit(f,bit,flags):
        edges=(((i,j),(i+a,j+b),d) for i,j in product(range(n),repeat=2)
               for d,(a,b) in enumerate(DIR[:2]) if i+a<n and j+b<n)
        sels,selected=install(f,bit,edges,n,frames)
        f.append(list(sels.values()));guard=f.nv+1
        for code,sel in sels.items():
            marks=frames[code];q=[(0,0)];seen=set(q)
            for i,j in q:
                for a,b in DIR:
                    u=i+a,j+b
                    if u in marks and min(*u,n-1-u[0],n-1-u[1])==0 and u not in seen and (marks[i,j] or marks[u]):
                        q.append(u);seen.add(u)
            both=not {(0,n-1),(n-1,0),(n-1,n-1)}<=seen
            f.append([-sel,guard if both else -guard])
            for u,v in marks.items():f.append([-sel,bit(*u) if v else -bit(*u)])
        reverse_charge(f,bit,selected,n,data,guard)
        stem=Path(f'target/interior_connector_{n}');fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat');log=stem.with_suffix('.log')
        f.to_file(str(fn));print('full square',n,'frames',len(frames),'variables',f.nv,'clauses',len(f.clauses),flush=True)
        with log.open('w') as o:st=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(fn),str(pr)],stdout=o).returncode
        if st==20:
            res=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True)
            assert res.returncode==0 and b's VERIFIED' in res.stdout
            stem.with_suffix('.check').write_bytes(res.stdout);print('all ten UNSAT, s VERIFIED',flush=True)
        elif st==10:
            model={int(x) for l in log.read_text().splitlines() if l.startswith('v ') for x in l[2:].split()}
            rows=[''.join('#' if bit(i,j) in model else '.' for j in range(n)) for i in range(n)]
            k=(n-2)//3;score=verify(rows);assert score[0]==score[-1]==3*k*k+7*k-(k-5)//7
            stem.with_suffix('.forest').write_text('\n'.join(rows)+'\n');print('verified forest',score)
        else:print('no decision',st)
        pr.unlink(missing_ok=True)
    window(n,'rim',n,data,matching=True,exit_only=True,emit=emit)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
