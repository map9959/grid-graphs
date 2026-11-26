"""Bound entire triangles of physical C,j by affine integer dual prices."""
from .rank44_faces import test,table,colors


def audit():
    planes=test(replay=True,off=49,weighted=True,components=5,ranges=True)
    # Small palettes embed as partitions with unused colors. Test
    # inclusion of the actual dominant masks AND their physical ranks.
    for c in range(1,5):
        for j in range(c):
            for r in range(5):
                if r<2 and r!=j:continue
                sup=table(5,r)
                for (m,q),v in table(c,j).items():assert sup[m,colors(q)]==v
    assert table(4,2)==table(4,3)
    def upper(x,c,j,r):
        u,dx,dc,dj=planes[5,r]
        return u+dx*(x-2)+dc*(c-5)+dj*(j-r)
    def small(x,c,j):
        return min(upper(x,c,j,r) for r in range(5) if r==j or r>=2)
    # C cannot exceed the 35^2 junctions. A fixed affine bound takes
    # its maximum at a vertex of its triangle or segment.
    N=35**2
    sectors=[[(5,0),(N,0)],[(5,1),(N,1)],[(5,2),(N,2),(N,N-3)],
             [(5,3),(N,N-2)],[(5,4),(N,N-1)]]
    for x in range(2,6):
        low=max(small(x,c,j) for c in range(1,5) for j in range(c))
        high=max(max(upper(x,c,j,r) for c,j in vertices) for r,vertices in enumerate(sectors))
        print('X',x,'C < 5 upper',low,'C >= 5 upper',high,'scale',10**12,flush=True)
        assert max(low,high)<3647*10**12


if __name__=='__main__':audit()
