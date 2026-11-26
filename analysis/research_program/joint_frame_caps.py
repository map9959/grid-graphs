"""Transverse cap transfer with both side wings attached to their actual frame tooth."""
import subprocess
import re

def cap(n,h,L,R,arm,pins,price=7,clip=True,check=(),links=None,signature=False):
    """arm is the number of wing rows kept on this side of the transverse split."""
    end=n-1-R
    assert (end-L)%3==0
    ix={};es=[];fix=[];tags=[];cp=[]
    def node(k,m=-1,tag=0):
        if k in ix:return
        ix[k]=len(es);es.append([]);fix.append(m);tags.append(tag)
    def edge(u,v,always=False):
        i,j=sorted((ix[u],ix[v]));es[j].append((i,always))
    def root(x):
        t=('t',x);node(t,0,int(x in pins));return t
    def wing(y,x,side):
        t=root(side);q=(y,x);m=0 if abs(x-side)==1 else -1
        cut=links is not None and y==h+arm-1 and x in (0,n-1)
        if cut and not links[int(x!=0)]:m=0
        node(q,m,int(cut and links[int(x!=0)]))
        if abs(x-side)==1:edge(q,t,True)
        for u in ((y-1,x),(y+1,x),(y,x-1),(y,x+1)):
            if u in ix:edge(q,u)
    for j,y in enumerate(reversed(range(h,h+arm))):
        for x in range(L):wing(y,x,L)
        if ('left',j) in check:cp.append(len(es)-1)
    for x in range(n):
        # Introduce each pitch terminal on its first incident cap column.
        if L<=x<=end:t=root(L+3*((x-L+1)//3))
        for y in range(h):
            q=(y,x);node(q)
            if x:edge(q,(y,x-1))
            if y:edge(q,(y-1,x))
            if y==h-1:
                if L<=x<=end:edge(q,t,(x-L)%3==0)
                elif (h,x) in ix:edge(q,(h,x))
        if x in check:cp.append(len(es)-1)
    for y in range(h,h+arm):
        for x in range(end+1,n):wing(y,x,end)
        if ('right',y-h) in check:cp.append(len(es)-1)
    N=len(es)
    if signature:
        last=list(range(N));live=[];out=[]
        for i,ls in enumerate(es):
            for j,_ in ls:last[j]=i
        for i,ls in enumerate(es):
            prev=tuple((live.index(j),always) for j,always in ls)
            live.append(i)
            keep=tuple(k for k,j in enumerate(live) if last[j]>i)
            out.append((fix[i],tags[i],prev,keep));live=[live[k] for k in keep]
        return out,cp
    inp=[N,*[z for ls in es for z in (len(ls),*(i+1+N*a for i,a in ls))],*fix,-2,*tags,*cp]
    res=subprocess.run(['target/annular_frontier','10',str(price),*(['--classes'] if clip else [])],
                       input=' '.join(map(str,inp)),text=True,capture_output=True)
    if res.returncode:raise RuntimeError(res.stderr)
    return ({int(k):int(v) for k,v in (s.split() for s in res.stdout.splitlines())}
            if clip else int(res.stdout.split()[0])),res.stderr

def upper(n,a,b,L,R,split,check=()):
    H=n-a-b;p=(n-L-R+2)//3;pins=set(range(L,n-R,3))
    from itertools import product
    worst=0
    assert split and H>split and L>=2 and R>=2
    for links in product((0,1),repeat=2):
        if links==(1,0) and L==R:continue
        A,al=cap(n,a,L,R,split,pins,links=links,check=check)
        B,bl=cap(n,b,L,R,H-split,pins,links=links,check=check)
        if check:print(al,bl)
        q=p+sum(links)
        vals=[(A[2]+B[2]-7*(q+1))//10,
              (A[1]-7)//10+(B[2]-7*q)//10,(B[1]-7)//10+(A[2]-7*q)//10,
              (A[1]-7)//10+(B[1]-7)//10+1-q]
        print(links,'cap prices',A,B,'uppers',*[H*p+z for z in vals],flush=True)
        worst=max(worst,H*p+max(vals))
    return worst

def family():
    from .comb_cap_transfer import construct
    from .extend_forest_28 import verify
    for n in range(103,155,3):
        k=n//3;H=n-18;D=30;p=k-1
        pins=range(3,n-3,3);assert len(pins)==p
        nb=n>=127;worst=0
        for links in ((0,0),(0,1),(1,1)):
            cp=[('left',15),('left',16),('right',15),('right',16)]
            if nb:cp.extend([90,120])
            A,log=cap(n,9,3,3,D,pins,links=links,check=cp)
            tests=re.findall(r'same (true|false) dominated \w+ shift (\d+)',log)
            assert tests[0]==tests[-1]==('true','10')
            if nb:assert tests[2]==('true','1000')
            B={j:v+20*(H-2*D) for j,v in A.items()}
            q=p+sum(links)
            vals=[(A[2]+B[2]-7*(q+1))//10,
                  (A[1]-7)//10+(B[2]-7*q)//10,
                  (B[1]-7)//10+(A[2]-7*q)//10,
                  (A[1]-7)//10+(B[1]-7)//10+1-q]
            worst=max(worst,H*p+max(vals))
        comb=3*k*k+5*k+(3*k-13)//10
        assert worst==comb,(n,worst,comb)
        rows=construct(n,4)
        assert all((rows[y][x]=='#')==(x%3==0) for y in (9,n-10) for x in range(3,n-3))
        assert all(rows[y][3]==rows[y][n-4]=='#' for y in range(9,n-9))
        tree=verify(rows);assert tree[0]==tree[-1]==comb
        print(n,'joint upper and tree',comb,'width pump' if nb else 'finite base',flush=True)
if __name__=='__main__':
    import sys
    if '--family' in sys.argv:family()
    else:upper(*map(int,sys.argv[1:]))
