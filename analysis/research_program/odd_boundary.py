"""Checked, local boundary requirements for any one-defect 35+42t forest."""
from .defect_window import table,window,product
from pathlib import Path
import subprocess

def run():
    n=119;R=5;B=R+7;M=n//2;tables=table(n)
    for region in ('root','edge','corner'):
        def emit(f,bit,flags):
            if region=='corner':
                vv=[bit(0,1),bit(0,2),bit(1,0),bit(2,0)]
                for w in ((0,0,1,1),(0,1,1,1),(1,1,0,0),(1,1,0,1)):
                    f.append([-v if b else v for v,b in zip(vv,w)])
            else:
                js=range(3,B) if region=='root' else range(M,M+3)
                f.append([-bit(0,j) for j in js])
            fn=Path('target/odd_boundary_'+region+'.cnf');proof=fn.with_suffix('.drat');f.to_file(str(fn))
            s=subprocess.run(['target/cadical/build/cadical',str(fn),str(proof)],capture_output=True)
            assert s.returncode==20,(region,s.returncode)
            z=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(proof)],capture_output=True)
            assert z.returncode==0 and b's VERIFIED' in z.stdout
            print(region,'variables',f.nv,'clauses',len(f.clauses),'s VERIFIED',flush=True)
            proof.unlink()
        window(n,'root' if region=='corner' else region,R,tables,free_defect=True,emit=emit)
if __name__=='__main__':run()
