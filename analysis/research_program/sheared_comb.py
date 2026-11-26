"""Off-phase comb fields meeting along a free oblique strip and two free caps."""
from .elbow_cap import contracted,run

def solve(n,h,p,shift,offset=0):
    free=[];F=set()
    for x in range(n):
        # Across three columns move the seam by `shift` rows.
        start=min(n-2,max(2,(n-2-h)//2+(x-n//2)*shift//3+offset))
        for y in range(n):
            u=y*n+x
            if start<=y<start+h or n-6<=y<n-2:free.append(u)
            elif y in (0,n-1) or 2<=y<n-2 and x%3==(p if y<start else 0):F.add(u)
    try:data,k0=contracted(n,free,F)
    except AssertionError:print('fixed core cyclic',h,p,shift,offset);return
    z=run(['target/annular_frontier'],input=' '.join(map(str,data)),text=True,capture_output=True)
    if z.returncode:print('resource limit',z.stderr);return
    mx,w,s=map(int,z.stdout.split());k=n//3
    print(n,h,p,shift,offset,'score',k0+mx,'over comb',k0+mx-3*k*k-5*k-(3*k-13)//10,'width',w,'states',s,flush=True)
if __name__=='__main__':
    import sys
    solve(*map(int,sys.argv[1:]))
