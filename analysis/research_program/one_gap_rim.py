"""Search a grounded perimeter: a single unforced edge fixed by D4 symmetry."""
from .defect_window import table,window
from .odd_frames import frame,trans,DIR,product
import sys

def run(n,R,skeleton=0):
    # Every allowed frame here has the same perimeter path, with its
    # missing edge from (0,1) to (0,2). Accordingly all path arrows agree.
    words=[(0,)+w for w in product((1,3),repeat=3)]
    m=frame(n,words[0]);p={(0,0):-1};todo=[(0,0)]
    for i,j in todo:
        for d,(a,b) in enumerate(DIR):
            v=i+a,j+b
            if v in m and min(*v,n-1-v[0],n-1-v[1])==0 and v not in p and (m[i,j] or m[v]):
                todo.append(v);p[v]=(d+2)%4
    assert len(p)==4*n-4
    def query(s,bit):
        ans=[]
        for w in words:
            m=frame(n,w)
            if s.solve(assumptions=[bit(*pos) if z else -bit(*pos) for pos,z in m.items()]):ans.append(w)
            print('frame',w,'survives',w in ans,flush=True)
        return ans
    print('side',n,'rim',R,window(n,'rim',R,table(n),True,False,True,query,free_defect=True,orient=p,skeleton=skeleton))
if __name__=='__main__':run(*map(int,sys.argv[1:]))
