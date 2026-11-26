"""Full frontier-vector recurrence on both arms of the partial-profile elbow."""
from .elbow_cap import build,run

def audit():
    for n in range(88,118,3):
        k=n//3
        cap=None
        for cut,inc in (([(y,5) for y in (25,55)],60), ([(n-1,x) for x in (44,74)],73)):
            data,core=build(n,6,7,check=cut)
            r=run(['target/annular_frontier'],input=' '.join(map(str,data)),text=True,capture_output=True,check=True)
            assert f'same true dominated true shift {inc}' in r.stderr
            z=int(r.stdout.split()[0])
            assert cap in (None,z);cap=z
        assert cap+core==3*k*k+5*k+(3*k-13)//10
        print(n,core,cap,'both arm vectors repeat',flush=True)
if __name__=='__main__':audit()
