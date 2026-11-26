"""A turn's two perpendicular coarse edges must coexist on the SAME face mask."""
from collections import Counter,defaultdict
from itertools import product
import json
from pathlib import Path
from .skeleton_wired_faces import face_masks
from .patch_square import trans
from .skeleton_exit_chart import model
from .coarse_incident_lift import lift


def geometry(n):
    def axis(z,S,h):return z if z<h else 2*h+3+z-S if z>=S-h else h+(z-h)%3
    def face(y,x):return axis(y,n-3,2),axis(x,n-3,2),0,0
    def pos(y,x):return (axis(y,n,8),axis(x,n,8),max(-9,min(9,y-x)),max(-9,min(9,y+x+1-n)))
    jj={pos(i,j):(i,j) for i,j in product(range(0,n,3),repeat=2)}
    ff={face(i,j):(i,j) for i,j in product(range(0,n-3,3),repeat=2)}
    return face,pos,jj,ff


def couple(ns,A,b,n=103):
    face,pos,jj,ff=geometry(n)
    laws=defaultdict(Counter);ms=face_masks()
    for name,x in ns.items():
        if name[0]=='wiredFace':
            tag,m=name[1];i,j=ff[tag]
            imgs={(face(*trans(i,j,n-3,g)),q) for g,q in enumerate(ms[m][1])}
            for p,q in imgs:
                bit=lambda y,z:q>>(4*y+z)&1
                for a,z in product((0,3),repeat=2):
                    dx=1 if z==0 else -1;dy=1 if a==0 else -1
                    h=[bit(a,z+k*dx) for k in range(4)];v=[bit(a+k*dy,z) for k in range(4)]
                    path=lambda s:int(all(s[k] or s[k+1] for k in range(3)))
                    k=(p,a,z,h[0],h[1],v[1],path(h),path(v))
                    laws[k][x]+=1
        elif name[0]=='incident':
            _,f,(p,nb,o,mask)=name;i,j=jj[p];imgs=set()
            for g in range(8):
                rot=lambda s:((2-s if g&4 else s)+g)%4
                w=[9]*4
                for s in range(4):w[rot(s)]=nb[s]
                imgs.add((pos(*trans(i,j,n,g)),tuple(w),rot(o) if o>=0 else -1,
                          sum(1<<rot(s) for s in range(4) if mask>>s&1)))
            for q,v,_,bits in imgs:
                y,j=jj[q]
                for a,z in product((0,3),repeat=2):
                    if not(0<=y-a<n-3 and 0<=j-z<n-3):continue
                    hd=2 if z else 0;vd=3 if a else 1
                    k=(face(y-a,j-z),a,z,f,v[hd],v[vd],bits>>hd&1,bits>>vd&1)
                    laws[k][x]-=1
    for row in laws.values():
        A.append(([(x,v) for x,v in row.items() if v],'='));b.append(0)
    return list(laws)


def chart():
    ns,A,b,obj,bounds,_=model(103,4,4,43,edge_floor=True,lines=True,faces=True,isolate_cut=True)
    lift(ns,A,b,103,4,4)
    before=len(A);keys=couple(ns,A,b)
    return ns,A,b,obj,bounds,before,keys


def certify(save=False):
    ns,A,b,obj,bounds,before,keys=chart()
    # One projected statistic already suffices. At a vacant junction
    # with a marked inward H stub, a failed path is the word .#..
    # read inward along that side. Count it on both measurements.
    active={k for k in keys if k[3]==0 and k[4]==1 and k[6]==0}
    joint=Counter()
    for k,(row,op) in zip(keys,A[before:]):
        if k in active:
            for x,w in row:joint[x]+=w
    A=A[:before]+[([(x,v) for x,v in joint.items() if v],'=')];b=b[:before]+[0]
    path=Path(__file__).with_name('segment_face_floor_103_dual.json');scale=10**12
    if save:
        from .side28_score import solve
        score,dual,_=solve(A,b,obj,ns,interior=True,bounds=bounds)
        print('numerical',score,flush=True)
        y={i:round(v*scale) for i,v in enumerate(dual) if round(v*scale)}
        for i in list(y):
            if A[i][1]=='<=':y[i]=max(0,y[i])
            if A[i][1]=='>=':y[i]=min(0,y[i])
    else:y=dict(json.loads(path.read_text()))
    rc=Counter({x:v*scale for x,v in obj.items()});ub=0
    for i,v in y.items():
        row,op=A[i];assert op=='=' or (v>=0 if op=='<=' else v<=0)
        ub+=v*b[i]
        for x,w in row:rc[x]-=w*v
    repair=103**2*sum(v for x,v in rc.items() if v>0 and x not in bounds)
    ub+=repair
    print('exact conditional upper',f'{ub}/{scale}','including residual allowance',f'{repair}/{scale}',
          'rows',len(A),'variables',len(ns),flush=True)
    assert ub<3647*scale
    if save:path.write_text(json.dumps(sorted((i,v) for i,v in y.items() if v),separators=(',',':'))+'\n')
    # Extend the same observable to impossible signatures (zero mass
    # on both sides). Its price depends on no vertical bits.
    sites={key[:3] for key in keys};weights={
        (*site,*bits):y.get(before,0) if bits[0]==0 and bits[1]==1 and bits[3]==0 else 0
        for site in sites for bits in product(range(2),repeat=5)}
    # Without imposing the new equations, the old rows imply
    # scale*M <= ub + sum_key weights[key]*(face_count-incident_count).
    assert any(weights.values()) and not any(b[before:])
    return ub,scale,weights


if __name__=='__main__':
    import sys
    certify('--save' in sys.argv)
