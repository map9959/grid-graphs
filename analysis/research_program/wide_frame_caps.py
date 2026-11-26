"""A U-shaped cap around an uncontracted physical frame, swept through its bends."""
import subprocess
from itertools import product

def cap(n,h,w,arm,links,fee=7,inspect=(),pitch=False,clipped=True,near=False,ban=()):
    assert (n-1-2*w)%3==0
    end=n-1-w;yend=h+arm-1
    corner=sorted(((y,x) for y in range(h+1) for x in range(w+1)),key=lambda p:(p[1]-p[0],-p[0]))
    order=[(y,x) for y in reversed(range(h+1,yend+1)) for x in range(w+1)]
    order+=corner+[(y,x) for x in range(w+1,end) for y in range(h+1)]
    order += [(y,n-1-x) for y,x in reversed(corner)]
    order += [(y,x) for y in range(h+1,yend+1) for x in range(end,n)]
    ix={p:i for i,p in enumerate(order)};N=len(ix);assert N==len(order)
    edges=[];fix=[];tags=[];base=0
    for j,(y,x) in enumerate(order):
        prev=[ix[p]+1 for p in ((y-1,x),(y+1,x),(y,x-1),(y,x+1)) if ix.get(p,N)<j]
        edges.extend([len(prev),*prev]);f=-1;t=0
        if y>=h and w<=x<=end:
            f=int(x in (w,end) or (x-w)%3==0);base+=f;t=int(f and y==h)
        if y>=h and x in (w-1,end+1):f=0
        if pitch and y==yend and (x<w or x>end):
            f=int(min(x,n-1-x)%3==0);t=f
        elif links is not None and y==yend and x in (0,n-1):
            if links[int(x!=0)]:t=1
            else:f=0
        fix.append(f);tags.append(t)
    for j,(y,x) in enumerate(order):
        if fix[j]!=1:continue
        for dy,dx in product((-1,1),repeat=2):
            i=ix.get((y+dy,x+dx))
            if i is not None:assert fix[i]!=1;fix[i]=0
    bans=[]
    for y in ban:
        assert h<y<yend
        # The left wing is traversed before the cap. Its entire row,
        # unchanged and in order, is the frontier at this checkpoint.
        idx=ix[y,w];assert order[idx-w:idx+1]==[(y,j) for j in range(w+1)]
        bans.extend([idx,(1<<w)-1,sum(1<<j for j in range(0,w,3))])
    inp=[N,*edges,*fix,-2,*tags,*[ix[p] for p in inspect],-3,*bans]
    proc=subprocess.run(['target/annular_frontier','10',str(fee),*(['--packed'] if clipped else []),*(['--near'] if near else [])],
                        input=' '.join(map(str,inp)),text=True,capture_output=True)
    if proc.returncode:raise RuntimeError(proc.stderr)
    if not clipped:return int(proc.stdout.split()[0])-10*base,proc.stderr
    vals={int(k):int(v)-10*base for k,v in (s.split() for s in proc.stdout.splitlines())}
    return vals,proc.stderr

def bound(n,h,w):
    H=n-2*h;p=(n-2*w+2)//3;worst=0
    for links in ((0,0),(1,0),(1,1)):
        A,_=cap(n,h,w,H//2,links);B,_=cap(n,h,w,H-H//2,links);q=p+sum(links)
        u=max((A[2]+B[2]-7*(q+1))//10,(A[1]-7)//10+(B[2]-7*q)//10,
              (B[1]-7)//10+(A[2]-7*q)//10,(A[1]-7)//10+(B[1]-7)//10+1-q)
        worst=max(worst,H*p+u)
        print(n,h,w,links,A,B,H*p+u,flush=True)
    return worst

def pitch_bound(n,h,w):
    H=n-2*h;p=(n-2*w+2)//3;u=2*((w+2)//3);q=p+u
    A,_=cap(n,h,w,(H+1)//2,(),pitch=True)
    B=A if H%2 else cap(n,h,w,H//2+1,(),pitch=True)[0]
    U=max((A[2]+B[2]-7*(q+1))//10,(A[1]-7)//10+(B[2]-7*q)//10,
          (B[1]-7)//10+(A[2]-7*q)//10,(A[1]-7)//10+(B[1]-7)//10+1-q)
    print('common middle pitch slice',n,A,B,H*p+U-u,flush=True)
    return H*p+U-u

def family():
    from .collar_vacancies import comb
    import re
    for n in range(103,133,3):
        a=19;h=w=9;H=n-18;p=(H+2)//3;q=p+6
        pos=[(h+a-1-15,w),(h+a-1-16,w),(h,60),(h,90)]
        price,log=cap(n,h,w,a,(),pitch=True,inspect=pos)
        checks=re.findall(r'packed checkpoint \d+ same (\w+) shift (\d+)',log)
        print(n,price,checks,flush=True)
        assert checks[0]==('true','40') and checks[-1]==('true','1100')
        # Both physical wing splits may be chosen independently. Each
        # complete side has H rows; one shared cut row is counted twice.
        shift=30*(2*(H+1)-4*a)
        # The total arm shift is a multiple of ten in every score floor.
        U=H*p+shift//10-6+max((2*price[2]-7*(q+1))//10,
              (price[1]-7)//10+(price[2]-7*q)//10,2*((price[1]-7)//10)+1-q)
        print('all sufficiently interior pitch cuts',U,'comb',comb(n),flush=True)
        assert U<=comb(n)

def no_pitch(n,checks=True):
    H=n-18;p=(H+2)//3;h=w=9;arm=42
    start=h+arm-1
    check=[(start-37,w),(start-38,w)]+([(h,90),(h,120)] if n>=133 else [])
    A,log=cap(n,h,w,arm,None,inspect=check if checks else (),ban=range(start-23,start))
    print(n,'absent left cut',A,log if checks else '',flush=True)
    if checks:
        import re
        pairs=re.findall(r'packed checkpoint \d+ same (\w+) shift (\d+)',log)
        assert pairs[0]==('true','40')
        if n>=133:assert pairs[-1]==('true','1100')
    # If the two wing-length checkpoints pump, a split with both half
    # lengths >=42 has this paired price plus its extra free wing rows.
    delta=6*(H-2*arm)
    vals=[(2*A[2]-7*(p+1))//10,(A[1]-7)//10+(A[2]-7*p)//10,
          2*((A[1]-7)//10)+1-p]
    return H*p+delta+max(vals)

def absent_family():
    from .collar_vacancies import comb
    # Reflecting the whole piece, the unrestricted wing can go first.
    # Its recurring prefix does not depend on the subsequent cap.
    _,log=cap(31,3,9,42,None,inspect=[(44-15,9),(44-16,9)])
    assert 'same true shift 40' in log
    for n in range(103,163,3):
        u=no_pitch(n);assert u<=comb(n)
        print('frame missing a central wing cut:',u,comb(n),flush=True)

if __name__=='__main__':
    import sys
    args=sys.argv[1:]
    if args==['--family']:family()
    elif args==['--absent-family']:absent_family()
    elif '--absent' in args:print('pumped upper',no_pitch(int(args[0])))
    else:print('bound',(pitch_bound if '--pitch' in args else bound)(*map(int,(v for v in args if v!='--pitch'))))
