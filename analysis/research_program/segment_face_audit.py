"""Check the actual physical-to-bucket map of the added face-corner equations."""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from .segment_face_turns import chart,geometry
from .skeleton_wired_faces import face_masks
from .skeleton_cross_rank import graphs
from .cross_minor_price import verify
from .patch_square import trans
from .skeleton_exit_chart import DIR


def audit():
    n=103;dom=range(0,n,3);face,pos,jj,ff=geometry(n)
    ns,A,b,_,_,base,_=chart()
    # Every translated junction in one fine type yields the same terms
    # on coarsening, including each boundary-clipped list of adjacent faces.
    def around(i,j):return [(face(i-a,j-z),a,z) for a,z in product((0,3),repeat=2)
                             if 0<=i-a<n-3 and 0<=j-z<n-3]
    for i,j in product(dom,repeat=2):
        assert around(i,j)==around(*jj[pos(i,j)])
        if i<n-3 and j<n-3:
            p=ff[face(i,j)]
            for g in range(8):
                assert face(*trans(i,j,n-3,g))==face(*trans(*p,n-3,g))
                for a,z in product((0,3),repeat=2):
                    u,v=trans(i+a,j+z,n,g);x,y=trans(i,j,n-3,g)
                    assert (u-x,v-y)==trans(a,z,4,g)
    cases=0
    for m,(_,imgs) in face_masks().items():
        for g in range(8):
            # Direct edge-set path checks on each transformed face;
            # transport three ordered unit edges, including their ends.
            for a,z in product((0,3),repeat=2):
                for dy,dx in ((0,1 if z==0 else -1),(1 if a==0 else -1,0)):
                    pts=[(a+k*dy,z+k*dx) for k in range(4)]
                    before=[(m>>(4*u+v))&1 for u,v in pts]
                    after=[(imgs[g]>>(4*u+v))&1 for u,v in [trans(*t,4,g) for t in pts]]
                    assert before==after
                    cases+=1
    # Independently construct physical orbit frequencies by rotating the
    # entire mark board and rooted tree, not by expanding each atom in `couple`.
    board=['#'*n,'.'*n]+['#..'*34+'#']*(n-2)
    assert verify(board)==(3638,10608,1,10608,3638)
    adj=[[] for _ in range(n*n)]
    for u,v in graphs(board):adj[u].append(v);adj[v].append(u)
    parent={0:-1};todo=[0]
    for u in todo:
        for v in adj[u]:
            if v not in parent:todo.append(v);parent[v]=u
    assert len(todo)==n*n
    freq=Counter()
    for g in range(8):
        r=[['.']*n for _ in range(n)];pars={}
        for i,j in product(range(n),repeat=2):
            u,v=trans(i,j,n,g);r[u][v]=board[i][j];par=parent[i*n+j]
            if par>=0:pars[u,v]=trans(*divmod(par,n),n,g)
        bonds=set(graphs(r))
        for i,j in product(dom,repeat=2):
            if i<n-3 and j<n-3:
                mask=sum((r[i+a][j+z]=='#')<<(4*a+z) for a,z in product(range(4),repeat=2))
                name='wiredFace',(face(i,j),mask)
                if name in ns:freq[ns[name]]+=Q(1,8)
            nb=[];mask=0;o=-1
            for d,(dy,dx) in enumerate(DIR):
                a,z=i+dy,j+dx
                if (a,z)==pars.get((i,j)):o=d
                if not(0<=a<n and 0<=z<n):nb.append(9);continue
                nb.append(int(r[a][z]=='#'))
                path=[(i+t*dy)*n+j+t*dx for t in range(4)]
                if all(tuple(sorted(edge)) in bonds for edge in zip(path,path[1:])):mask+=1<<d
            name='incident',int(r[i][j]=='#'),(pos(i,j),tuple(nb),o,mask)
            if name in ns:freq[ns[name]]+=Q(1,8)
    for (row,op),rhs in zip(A[base:],b[base:]):
        assert op=='=' and rhs==sum(w*freq[x] for x,w in row)==0
    print('coordinate audit: 1225 junctions, 1156 faces;',cases,'transformed paths; physical tree agrees on',
          len(A)-base,'new marginal equations')


if __name__=='__main__':audit()
