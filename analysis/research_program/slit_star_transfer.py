"""Shorten four boundary channels but retain the 2-D blocks right up to a slit."""
from itertools import product
import sys
from .depth_two_far_quarter import run
from .defect_window import table
from .shorten_245_star import audit,nb
from .joint_rim_pump import kernel
from .odd_frames import frame
from functools import lru_cache
from pathlib import Path
import gzip

@lru_cache(None)
def frame_path(n,w):
    m=frame(n,(0,*list(product((1,3),repeat=3))[w%8]))
    if w>=8:m={(j,i):b for (i,j),b in m.items()}
    root=(n-1,n-1);path={root:-1};q=[root]
    for u in q:
        for d in range(4):
            v=nb(u,d)
            if min(*v,n-1-v[0],n-1-v[1])!=0 or v in path or not(m[v] or m[u]):continue
            path[v]=(d+2)%4;q.append(v)
    return m,path

def region(n,cuts,starts):
    delta=n-203
    # Bulk is deleted only on the slit; at depth 7 a lip separates the
    # flexible strip from the bulk until both the slit and pump have ended.
    def keep(long,trans,cut,start):
        normal=min(trans,n-1-trans)
        if normal<7:return True
        if cut<=long<=cut+delta:return False
        return normal!=7 or not min(cut,start-2)<=long<=max(cut,start+38)+delta
    return {(i,j) for i,j in product(range(n),repeat=2)
            if keep(i,j,cuts[0],starts[0]) and keep(j,i,cuts[1],starts[1])}

def test(group,seconds):
    # Normalize the star to north and allow either opening (16 frames).
    # The slit need not align with the pump; that permits keeping larger
    # intact corners than cutting out the full width of the corridor.
    if group=='late':
        cuts=(194,9);starts=(150,12)
        large=[d for d in range(143,240,3) if d%6==5 or d>194]
    elif group=='early':
        cuts=(194,194);starts=(150,150);large=list(range(5,143,6))
    else:raise ValueError(group)
    small=[d-42 if group=='late' else d for d in large]
    A=region(203,cuts,starts);B=region(245,cuts,starts)
    # Exact geometric/type comparison outside the four replaceable pieces.
    # For bulk vertices use the interior slit. For points in the
    # 7-lane strip shift the suffix starting at the right interface.
    T=table(203)[0];U=table(245)[0]
    def shift(p):
        i,j=p
        def ax(u,v,k):
            cut=starts[k]+36 if min(v,202-v)<7 else cuts[k]
            return u+42*(u>=cut)
        return ax(i,j,0),ax(j,i,1)
    def middle(p):
        return any(min(p[1-k],202-p[1-k])<7 and starts[k]<=p[k]<starts[k]+36 for k in (0,1))
    mapped={shift(p) for p in A if not middle(p)}
    Bcore={p for p in B if not any(min(p[1-k],244-p[1-k])<7 and starts[k]<=p[k]<starts[k]+78 for k in (0,1))}
    assert mapped==Bcore
    for p in A:
        if middle(p):continue
        assert T(0,*p)==U(0,*shift(p))
        for a,b in ((0,1),(1,0),(1,1),(2,0),(0,2),(2,2)):
            q=p[0]+a,p[1]+b
            if q not in A or middle(q):continue
            # Only compare stencils wholly in the retained region.
            if all((p[0]+x,p[1]+y) in A and not middle((p[0]+x,p[1]+y)) for x,y in product(range(a+1),range(b+1))):
                assert shift(q)==(shift(p)[0]+a,shift(p)[1]+b)
                if (a,b)==(2,2):assert T(1,*p)==U(1,*shift(p))
    assert all(shift((2,d))==(2,e) for d,e in zip(small,large))
    for w in range(16):
        f,p=frame_path(203,w);g,q=frame_path(245,w)
        for u in f:
            if u in A and not middle(u):assert f[u]==g[shift(u)]
        for u in p:
            if not middle(u):assert p[u]==q[shift(u)]
        for axis in (0,1):
            for far in (False,True):
                def port(N,j):
                    r=N-1 if far else 0
                    return (j,r) if axis==0 else (r,j)
                a=starts[axis];dirs={p[port(203,j)] for j in range(a-1,a+38)}
                assert dirs=={q[port(245,j)] for j in range(a-1,a+80)} and len(dirs)==1
                assert dirs<=({1,3} if axis==0 else {0,2})
    print(group,'retained domain vertices',len(B),'->',len(A),'star distances',large,'->',small,flush=True)
    archive=Path(__file__).with_name('one_gap_projection_examples')/f'slit203_{group}.gz'
    def replay(w,site,X,out):
        v,e,cc=audit(203,A,X,out,site,None,table(203),frame_path(203,w),(202,202))
        # A channel owns its longitudinal edges and the vertical edges of
        # every newly added column. Its first column is identified with the
        # permanent ports; its vertical edges are owned by the exterior.
        Z={};loops=[]
        for axis in (0,1):
            for far in (False,True):
                def pt(n,r,j):
                    t=n-1-r if far else r
                    return (j,t) if axis==0 else (t,j)
                start=starts[axis];back=3-axis
                def mask(j):return sum((pt(203,r,j) in X)<<r for r in range(7))
                _,_,extend=kernel(7);p=tuple(range(7))*2;seen={};choices=[]
                for j in range(start,start+37):
                    west=sum((out.get(pt(203,r,j))==back)<<r for r in range(7))
                    key=(j%3,mask(j-1),mask(j),west,p)
                    for prev in seen.get(key,[]):
                        if 42%(j-prev)==0:choices.append((prev,j-prev))
                    seen.setdefault(key,[]).append(j)
                    if j<start+36:
                        p=extend(mask(j),mask(j+1),p)
                        assert p is not None
                assert choices,(axis,far,'no simple repeat in this specific word')
                first,length=min(choices,key=lambda t:(t[1],t[0]));loops.append((first,length))
                for j in range(start,start+78):
                    old=j if j<first else first+(j-first)%length if j<first+42 else j-42
                    for r in range(7):Z[pt(245,r,j)]=pt(203,r,old)
        Z.update({shift(p):p for p in A if not middle(p)})
        assert set(Z)==B
        Y={p for p,u in Z.items() if u in X};o2={p:out[u] for p,u in Z.items() if u in out}
        big=(2,large[small.index(site[1])])
        vv,ee,dd=audit(245,B,Y,o2,big,None,table(245),frame_path(245,w),(244,244))
        corr={(cc[u],dd[shift(u)]) for u in A if not middle(u)}
        assert len(corr)==len({a for a,b in corr})==len({b for a,b in corr})
        print('literal 42-step physical replay:',big,'->',site,'frame',w,'cycles 0, charges 72 only at star;',
              'channel repeat (start,length)',loops,'unchanged exterior classes',len(corr),
              'forced edges',ee,'->',e,flush=True)
        # Restoring even an UNmarked missing vertex forces its incident
        # edges to already marked neighbors. Look for a cycle independent
        # of all choices of missing bits, specifically across a slit that
        # widens by 42 in the donor. The two terminals remain connected
        # before and after the shortening.
        shortcuts=[]
        for u in sorted(set(product(range(203),repeat=2))-A):
            for d in (0,1):
                a,b=nb(u,d),nb(u,d+2)
                if a not in X or b not in X or cc[a]!=cc[b] or middle(a) or middle(b):continue
                fa,fb=shift(a),shift(b)
                if sum(abs(x-y) for x,y in zip(fa,fb))==44:
                    assert dd[fa]==dd[fb]
                    shortcuts.append((u,a,b,fa,fb))
        print('unavoidable single-vertex cycle closures across the shortened slits:',len(shortcuts),
              'example',next(iter(shortcuts),None),flush=True)
        if not archive.exists():
            raw=bytes([w,site[0],site[1]])+bytes((int(u in X)*5+out.get(u,-1)+1) for u in sorted(A))
            archive.write_bytes(gzip.compress(raw,mtime=0))
    if seconds==-1:
        raw=gzip.decompress(archive.read_bytes());w,i,j=raw[:3];data=dict(zip(sorted(A),raw[3:],strict=True))
        replay(w,(i,j),{u for u,b in data.items() if b>=5},{u:b%5-1 for u,b in data.items() if b%5})
    else:
        run(203,min(small),max(small),seconds,domain=A,distances=small,output=f'target/slit_star_245_{group}',replay=replay)
if __name__=='__main__':test(sys.argv[1],int(sys.argv[2]))
