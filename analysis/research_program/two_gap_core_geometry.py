"""Which physical parts of the side-245 two-gap proof are actually used?"""
from pathlib import Path
from collections import Counter
from .defect_window import window,table
import inspect

def run():
    n=245;stem=Path('target/two_gap_245_all_axis')
    cs=[tuple(map(int,l.split()[:-1])) for l in stem.with_suffix('.core').read_text().splitlines() if l and not l.startswith(('c','p'))]
    used={abs(z) for c in cs for z in c}
    def emit(f,bit,flags):
        vp=inspect.getclosurevars(bit).nonlocals['vp'];verts={};kind=Counter()
        for z in used:
            u=vp.obj(z);key=u[0] if isinstance(u,tuple) else 'global';kind[key]+=1
            if isinstance(u,tuple) and len(u)>=3:verts[z]=u[1:3]
        print('physical core variables',dict(kind))
        p=set(verts.values())
        for tag in ('ext','face'):
            pts={verts[z] for z in verts if vp.obj(z)[0]==tag}
            print(tag,'min and max depth',min(min(*u,n-1-u[0],n-1-u[1]) for u in pts),
                  max(min(*u,n-1-u[0],n-1-u[1]) for u in pts))
        # How far from each end is the active central portion of a side?
        for k in (0,3,9,18,27,36,45):
            print('depth',k,'top active range',min((j for i,j in p if i==k),default=-1),
                  max((j for i,j in p if i==k),default=-1))
        dist=lambda i:min(i,n-1-i)
        counts=Counter((dist(i)//10,dist(j)//10) for i,j in p)
        for k in range(13):print(' '.join(f'{counts[k,l]:4}' for l in range(13)))
        from .odd_frames import rotate,frame
        reps=[w for w in __import__('itertools').product(range(4),repeat=4) if sum(x in (0,2) for x in w)==2 and min(rotate(w,g) for g in range(8))==w]
        nv=f.nv
        print('base nv',nv,'axis clauses',sum(any(abs(z)>nv+len(reps) for z in c) for c in cs))
        for wnum,w in enumerate(reps,1):
            sel=nv+wnum
            units={c[1] if c[0]==-sel else c[0] for c in cs if len(c)==2 and -sel in c}
            tested=[]
            for s in __import__('itertools').product((1,3),repeat=3):
                m=frame(n,(0,*s))
                if all((atom:=vp.obj(abs(z)))[0]!='v' or m[atom[1:]]==int(z>0) for z in units):tested.append('0'+''.join(map(str,s)))
            print('frame',w,'guarded core units',len(units),'matching one-gap words',tested)
            literals=[(vp.obj(abs(z))[1:],int(z>0)) for z in units if vp.obj(abs(z))[0]=='v']
            others={}
            from itertools import product
            for place in range(4):
                for ww in product(*[(0,2) if t==place else (1,3) for t in range(4)]):
                    # Only the nonconstant corner bits need to be checked.
                    dd=dict(frame(17,ww))
                    def match(u,b):
                        i,j=(v if v<3 else (v-n+17 if v>=n-3 else 8) for v in u)
                        return dd[i,j]==b
                    if all(match(u,b) for u,b in literals):others.setdefault(place,[]).append(ww)
            print('possible gap corners for this core selector',sorted(others))
        # Over a band, check support well away from both parallel sides.
        for cut in (40,70,100,120,145,170,200):
            for axis in range(2):
                lane=sorted({u[1-axis] for u in p if cut<=u[axis]<cut+3})
                groups=[]
                for v in lane:
                    if groups and groups[-1][1]==v-1:groups[-1][1]=v
                    else:groups.append([v,v])
                print('axis',axis,'cut',cut,'occupied transverse intervals',groups)
    window(n,'rim',n,table(n),matching=True,emit=emit,exit_only=True)
if __name__=='__main__':run()
