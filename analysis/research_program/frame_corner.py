"""Corner-window tests with a prescribed perimeter path to the chosen root."""
from .odd_frames import frame,PAT
from .defect_window import window,table,DIR,trans
from functools import lru_cache
from itertools import product

def run():
    n=119;R=7;size=2*R+10;t=table(n)
    @lru_cache(None)
    def sat(bitset,arrows,root,paid):
        def impose(s,b):
            return s.solve(assumptions=[b(i,j) if v else -b(i,j) for i,j,v in bitset])
        return window(n,'root' if root else 'other',R,t,paid,query=impose,free_defect=True,orient=dict(arrows))
    for tail in product((1,3),repeat=3):
        w=(0,)+tail;marks=frame(n,w);status=[]
        for g in range(4):
            r=trans(0,0,n,g);q=[r];par={r:-1}
            for i,j in q:
                for d,(a,b) in enumerate(DIR):
                    x,y=i+a,j+b
                    if (x,y) in marks and min(x,y,n-1-x,n-1-y)==0 and (x,y) not in par and (marks[i,j] or marks[x,y]):
                        q.append((x,y));par[x,y]=(d+2)%4
            assert len(par)==4*n-4
            local=[]
            for h in range(4):
                bits=[];dirs=[]
                for a,b in product(range(size),repeat=2):
                    u=trans(a,b,n,h)
                    if u in marks:bits.append((a,b,marks[u]))
                    if u in par:dirs.append(((a,b),(par[u]-h)%4 if par[u]>=0 else -1))
                v=next((i for i in (0,1) if sat(tuple(bits),tuple(dirs),h==g,bool(i))),2);local.append(v)
            status.append(local)
        print(w,'necessary charged corners by root',status,flush=True)
if __name__=='__main__':run()
