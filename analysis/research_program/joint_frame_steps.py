"""Check the exact local graph instructions at the three independent pumping cuts."""
from .joint_frame_caps import cap

def audit():
    cases=0
    for n in range(103,155,3):
        for links in ((0,0),(1,0),(0,1),(1,1)):
            wide=n>=127
            cp=[('left',15),('left',16),('right',15),('right',16)]
            if wide:cp.extend([90,120])
            def graph(N,arm):
                return cap(N,9,3,3,arm,range(3,N-3,3),links=links,check=cp,signature=True)
            base,ids=graph(n,30)
            for delta,extra in ((0,1),(30,0),(30,1)):
                if delta and not wide:continue
                enlarged,_=graph(n+delta,30+extra)
                expected=base.copy()
                for j in reversed(range(0,len(ids),2)):
                    if (extra if j==0 or j==len(ids)-2 else delta):
                        a,b=ids[j:j+2];expected[b+1:b+1]=base[a+1:b+1]
                assert expected==enlarged
                cases+=1
    print(cases,'exact live-frontier instruction sequences equal after insertion')
if __name__=='__main__':audit()
